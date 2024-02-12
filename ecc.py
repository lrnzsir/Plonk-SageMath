"""
Wrapper for the py_ecc.optimized_bn128 module that implements the pairing-friendly elliptic curve bn128. \\
See https://hackmd.io/@jpw/bn254 for more information on the curve.
"""

from typing import Any, Iterable


# ---------------------------------------------
# BN128 Curve Parameters


class BN128:  # aka BN254
    """ Wrapper for the parameters of the elliptic curve bn128 """
    __z = 4965661367192848881

    @classmethod
    def z(cls):
        return cls.__z

    @classmethod
    def p(cls):
        """ Return the order of the field """
        return 36 * cls.__z**4 + 36 * cls.__z**3 + 24 * cls.__z**2 + 6 * cls.__z + 1
    
    @classmethod
    def r(cls):
        """ Return the order of the curve """
        return 36 * cls.__z**4 + 36 * cls.__z**3 + 18 * cls.__z**2 + 6 * cls.__z + 1
    
    @classmethod
    def t(cls):
        """ Return the order of the trace of Frobenius """
        return 6 * cls.__z**2 + 1
    
    @classmethod
    def Fp(cls):
        """ Return the field of the curve """
        from sage.all import GF
        return GF(cls.p())

    @classmethod
    def Fp2(cls):
        """ Return the extension field of the curve """
        from sage.all import GF
        w = cls.Fp()["w"].gen()
        return GF(cls.p()**2, name="w", modulus=w**2 + 1)
    
    @classmethod
    def Fp12(cls):
        """ Return the extension field of the extension field of the curve """
        from sage.all import GF
        w = cls.Fp2()["w"].gen()
        return GF(cls.p()**12, name="w", modulus=(w**6 - 9)**2 + 1)


_p = BN128.p()
_r = BN128.r()
_Fp = BN128.Fp()
_Fp2 = BN128.Fp2()
_Fp12 = BN128.Fp12()


# ---------------------------------------------
# Scalar Multiplication Algorithms


def __add(p1: tuple, p2: tuple) -> tuple:
    if p1[2] == 0:
        return p2
    if p2[2] == 0:
        return p1
    
    # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl

    x1, y1, z1 = p1
    x2, y2, z2 = p2

    z1_squared = z1**2
    z2_squared = z2**2
    
    u1 = x1 * z2_squared
    u2 = x2 * z1_squared

    z1_cubed = z1_squared * z1
    z2_cubed = z2_squared * z2
    
    s1 = y1 * z2_cubed
    s2 = y2 * z1_cubed

    if u1 == u2 and s1 == s2:  # if the points are equal
        return __double(p1)
    
    h = u2 - u1
    i = (h + h)**2
    j = h * i
    r = s2 - s1
    r = r + r
    v = u1 * i

    x3 = r**2 - j - v - v
    s1_j = s1 * j
    y3 = r * (v - x3) - (s1_j + s1_j)
    z3 = ((z1 + z2)**2 - z1_squared - z2_squared) * h

    return (x3, y3, z3)


def __double(p1: tuple) -> tuple:
    """ Return the double of the point (computed using  """
    x1, y1, z1 = p1

    if z1 == 0:
        return p1

    # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    
    a = x1**2
    b = y1**2
    c = b**2
    d = (x1 + b)**2 - a - c
    d = d + d
    e = a + a + a
    f = e**2
    x3 = f - (d + d)
    _8c = c + c
    _8c = _8c + _8c
    _8c = _8c + _8c
    y3 = e * (d - x3) - _8c
    z3 = y1 * z1
    z3 = z3 + z3

    return (x3, y3, z3)


def __to_affine(p1: tuple) -> tuple:
    """ Return the affine representation of the point """
    global _Fp
    x1, y1, z1 = p1
    if z1 == 0:
        return (x1, y1, z1)
    z1_inv = z1**-1
    z1_inv_squared = z1_inv**2
    return (x1 * z1_inv_squared, y1 * z1_inv_squared * z1_inv, _Fp(1))


def __affine_add(p1: tuple, p2: tuple) -> tuple:
    """ Return the addition of the two points where p1 is in affine coordinates """

    if p1[2] == 0:
        return p2
    if p2[2] == 0:
        return p1
    
    # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
    
    x2, y2, z2 = p1
    x1, y1, z1 = p2

    z1_squared = z1**2
    u2 = x2 * z1_squared
    s2 = y2 * z1 * z1_squared

    if u2 == x1 and s2 == y1:
        return __double(p1)
    
    h = u2 - x1
    h_squared = h**2
    i = h_squared + h_squared
    i = i + i
    j = h * i
    r = s2 - y1
    r = r + r
    v = x1 * i

    x3 = r**2 - j - (v + v)
    y1_j = y1 * j
    y3 = r * (v - x3) - (y1_j + y1_j)
    z3 = (z1 + h)**2 - z1_squared - h_squared

    return (x3, y3, z3)


def _scalar_multiplication(p1: tuple, scalar: int) -> tuple:
    """ Return the scalar multiplication of the point """
    
    if p1[2] == 0:  # if p1 is the zero point
        return p1
    if scalar == 0:
        return (0, 1, 0)  # the zero point
    if scalar < 0:
        scalar = -scalar  # negation of scalar
        p1 = (p1[0], -p1[1], p1[2])  # negation of p1
    if scalar == 1:
        return p1
    if scalar == 2:
        return __double(p1)
    
    p1 = __to_affine(p1)

    scalar_bits = tuple(map(int, bin(scalar)[2:]))
    result = p1
    for bit in scalar_bits[1:]:
        result = __double(result)
        if bit:
            result = __affine_add(p1, result)
    return result


def _optimized_scalar_multiplication(p1: tuple, scalar: int) -> tuple:
    """
    Return the scalar multiplication of the point
    
    Performs the same operations as _scalar_multiplication but does all operations in this function to minimize function calls overhead
    """
    global _Fp
    
    x1, y1, z1 = p1

    if z1 == 0:  # if p1 is the zero point
        return p1
    if scalar == 0:
        return tuple(map(_Fp, (0, 1, 0)))  # the zero point
    if scalar < 0:
        scalar = -scalar  # negation of scalar
        y1 = -y1  # negation of p1
    if scalar == 1:
        return p1
    if scalar == 2:
        # return __double(p1)
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        
        a = x1**2
        b = y1**2
        c = b**2
        d = (x1 + b)**2 - a - c
        d = d + d
        e = a + a + a
        f = e**2
        x3 = f - (d + d)
        _8c = c + c
        _8c = _8c + _8c
        _8c = _8c + _8c
        y3 = e * (d - x3) - _8c
        z3 = y1 * z1
        z3 = z3 + z3

        return (x3, y3, z3)

    # call __to_affine(p1)
    z1_inv = z1**-1
    z1_inv_squared = z1_inv**2
    x1 = x1 * z1_inv_squared
    y1 = y1 * z1_inv_squared * z1_inv
    z1 = 1
    p1 = (x1, y1, z1)
    
    scalar_bits = tuple(map(int, bin(scalar)[2:]))
    result = p1

    for bit in scalar_bits[1:]:
        # result = __double(result)
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l

        x2, y2, z2 = result
        
        a = x2**2
        b = y2**2
        c = b**2
        d = (x2 + b)**2 - a - c
        d = d + d
        e = a + a + a
        f = e**2
        x3 = f - (d + d)
        _8c = c + c
        _8c = _8c + _8c
        _8c = _8c + _8c
        y3 = e * (d - x3) - _8c
        z3 = y2 * z2
        z3 = z3 + z3

        result = (x3, y3, z3)

        if bit:  # result = __affine_add(p1, result)
            # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl
            
            x2, y2, z2 = p1
            x1, y1, z1 = result

            if z1 == 0:  # if result is the zero point
                result = p1
                continue

            z1_squared = z1**2
            u2 = x2 * z1_squared
            s2 = y2 * z1 * z1_squared

            if u2 == x1 and s2 == y1:  # return __double(p1)
                # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
                
                a = x1**2
                b = y1**2
                c = b**2
                d = (x1 + b)**2 - a - c
                d = d + d
                e = a + a + a
                f = e**2
                x3 = f - (d + d)
                _8c = c + c
                _8c = _8c + _8c
                _8c = _8c + _8c
                y3 = e * (d - x3) - _8c
                z3 = y1 * z1
                z3 = z3 + z3

                result = (x3, y3, z3)
            else: # continue | result = __affine_add(p1, result)
                # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-madd-2007-bl

                h = u2 - x1
                h_squared = h**2
                i = h_squared + h_squared
                i = i + i
                j = h * i
                r = s2 - y1
                r = r + r
                v = x1 * i

                x3 = r**2 - j - (v + v)
                y1_j = y1 * j
                y3 = r * (v - x3) - (y1_j + y1_j)
                z3 = (z1 + h)**2 - z1_squared - h_squared

                result = (x3, y3, z3)
    return result


# ---------------------------------------------
# Groups G1 and G2


class G1:
    """ Class for the points on the elliptic curve whose subgroup is G1 """
    bytes_size = 32  # the size of the bytes representation of the compressed point

    # field parameters
    __Fp = _Fp  # the field of the curve
    __Fp_order = _p  # the order of the field
    __Fp_zero = _Fp(0)  # the zero of the field
    __Fp_one = _Fp(1)  # the one of the field

    # curve parameters
    __curve_a = _Fp(0)  # the a coefficient of the curve
    __curve_b = _Fp(3)  # the b coefficient of the curve
    __curve_order = _r  # the order of the curve

    def __init__(self, x:int, y: int, z=_Fp(1), verify=True) -> None:
        if verify:
            x, y, z = map(self.__Fp, (x, y, z))
            if not self.is_on_curve(x, y, z):
                raise ValueError(f"({x}, {y}, {z}) is not on G1")
        self.x = x
        self.y = y
        self.z = z

    @classmethod
    def is_on_curve(cls, x: int, y: int, z=_Fp(1)) -> bool:
        x, y, z = map(cls.__Fp, (x, y, z))
        # equivalent to (y / z^3)^2 == (x / z^2)^3 + b
        return y**2 == x**3 + cls.__curve_b * z**6
    
    @classmethod
    def order(cls) -> int:
        """ Return the order of G1 """
        return cls.__curve_order
    
    @classmethod
    def generator(cls) -> "G1":
        """ Return the generator of the group G1 """
        return G1(cls.__Fp_one, cls.__Fp_one + cls.__Fp_one, verify=False)

    @classmethod
    def zero(cls) -> "G1":
        """ Return the zero of G1 """
        return G1(cls.__Fp_zero, cls.__Fp_one, cls.__Fp_zero, verify=False)
    
    def is_zero(self) -> bool:
        """ Return True if the point is the zero point """
        return self.z == self.__Fp_zero
    
    def to_affine(self) -> None:
        """ Return the affine representation of the point (from Jacobian to Weierstrass) """
        if self.z == self.__Fp_zero:  # if self is the zero point
            self.x = self.__Fp_zero
            self.y = self.__Fp_one
        else:
            z_inv = self.z**-1
            z_inv_squared = z_inv**2
            z_inv_cubed = z_inv * z_inv_squared
            self.x = self.x * z_inv_squared
            self.y = self.y * z_inv_cubed
            self.z = self.__Fp_one
    
    def to_bytes(self) -> bytes:
        """ Return the bytes representation of the point """
        return bytes(self)
    
    @classmethod
    def from_bytes(cls, data: bytes) -> "G1":
        """ Return the point from the bytes representation """
        if not isinstance(data, bytes):
            raise TypeError(f"Invalid bytes representation type: {type(data)}")
        if len(data) != 32:
            raise ValueError(f"Invalid bytes representation length: {len(data)}, expected 32 bytes")
        
        data = int.from_bytes(data, "big")
        if data == 0:
            return cls.zero()
        x = cls.__Fp(data % 2**254)
        try:
            y = (x**3 + cls.__curve_b).sqrt()
        except Exception:
            raise ValueError(f"Invalid bytes representation for G1: {hex(data)[2:].zfill(2 * cls.bytes_size)}")
        if data // 2**254 - 2 == int(y) & 1:
            return G1(x, y, cls.__Fp_one, verify=False)
        return G1(x, -y, cls.__Fp_one, verify=False)
    
    def __mul__(self, scalar: int) -> "G1":
        """ Return the scalar multiplication of the point """

        if getattr(scalar, "__int__", None) is None:
            raise TypeError(f"Multiplication is not defined for: G1 * {type(scalar)}")
        if not isinstance(scalar, int):
            scalar = int(scalar) % self.__curve_order

        # calls external function that does not use the class to make exponentiation faster
        x, y, z = map(self.__Fp, _optimized_scalar_multiplication((self.x, self.y, self.z), scalar))
        return G1(x, y, z, verify=False)
            
    def __rmul__(self, scalar: int) -> "G1":
        """ Return the scalar multiplication of the point """

        if getattr(scalar, "__int__", None) is None:
            raise TypeError(f"Multiplication is not defined for: G1 * {type(scalar)}")
        if not isinstance(scalar, int):
            scalar = int(scalar) % self.__curve_order
        
        # calls external function that does not use the class to make exponentiation faster
        x, y, z = map(self.__Fp, _optimized_scalar_multiplication((self.x, self.y, self.z), scalar))
        return G1(x, y, z, verify=False)
            
    def __add__(self, other: "G1") -> "G1":
        """ Return the addition of the two points """
        if not isinstance(other, G1):
            raise TypeError(f"Addition is not defined for: G1 + {type(other)}")
        
        if self.z == self.__Fp_zero:  # if self is the zero point
            return other
        if other.z == self.__Fp_zero:  # if other is the zero point
            return self
        
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        # self = (x1, y1, z1), other = (x2, y2, z2)

        z1_squared = self.z**2
        z2_squared = other.z**2
        
        u1 = self.x * z2_squared
        u2 = other.x * z1_squared

        z1_cubed = z1_squared * self.z
        z2_cubed = z2_squared * other.z
        
        s1 = self.y * z2_cubed
        s2 = other.y * z1_cubed

        if u1 == u2 and s1 == s2:  # if the points are equal
            return self.__double()
        
        h = u2 - u1
        i = (h + h)**2
        j = h * i
        r = s2 - s1
        r = r + r
        v = u1 * i

        x3 = r**2 - j - v - v
        s1_j = s1 * j
        y3 = r * (v - x3) - (s1_j + s1_j)
        z3 = ((self.z + other.z)**2 - z1_squared - z2_squared) * h

        return G1(x3, y3, z3, verify=False)
    
    def __double(self) -> "G1":
        """ Return the double of the point """
        if self.z == self.__Fp_zero:
            return self
        
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        # self = (x1, y1, z1)

        a = self.x**2
        b = self.y**2
        c = b**2
        d = (self.x + b)**2 - a - c
        d = d + d
        e = a + a + a
        f = e**2
        x3 = f - (d + d)
        _8c = c + c
        _8c = _8c + _8c
        _8c = _8c + _8c
        y3 = e * (d - x3) - _8c
        z3 = self.y * self.z
        z3 = z3 + z3

        return G1(x3, y3, z3, verify=False)

    def __neg__(self) -> "G1":
        """ Return the negation of the point """
        return G1(self.x, -self.y, self.z, verify=False)
    
    def __sub__(self, other: "G1") -> "G1":
        """ Return the subtraction of the two points """
        if not isinstance(other, G1):
            raise TypeError(f"Subtraction is not defined for: G1 - {type(other)}")
        return self.__add__(-other)
    
    def __eq__(self, other: "G1") -> bool:
        """ Return True if the points are equal """
        if not isinstance(other, G1):
            return False
        
        if self.z == self.__Fp_zero:  # if self is the zero point
            return other.z == self.__Fp_zero  # if other is the zero point
        if other.z == self.__Fp_zero:  # if other is the zero point
            return False  # self is not the zero point
        
        z1_squared = self.z**2
        z2_squared = other.z**2

        if self.x * z2_squared != other.x * z1_squared:
            return False
        
        z1_cubed = z1_squared * self.z
        z2_cubed = z2_squared * other.z

        return self.y * z2_cubed == other.y * z1_cubed
    
    def __ne__(self, other: "G1") -> bool:
        """ Return True if the points are not equal """
        return not self.__eq__(other)
    
    def __repr__(self) -> str:
        """ Return the string representation of the point """
        self.to_affine()
        return f"G1({self.x}, {self.y})"

    def __str__(self) -> str:
        """ Return the string representation of the point """
        return self.__repr__()
    
    def __bytes__(self) -> bytes:
        """ Return the bytes representation of the point in compressed form """
        self.to_affine()
        if self.z == self.__Fp_zero:
            return b"\x00" * 32
        return (((int(self.y) & 1) + 2) * 2**254 + int(self.x)).to_bytes(32, "big")
    
    def __iter__(self) -> Iterable:
        return iter((self.x, self.y, self.z))


class G2:
    """ Wrapper for the points on the elliptic curve whose subgroup is G2 """
    bytes_size = 32 * 2  # 32 for each compressed coordinate

    # field parameters
    __Fp2 = _Fp2  # the field of the curve
    __Fp2_order = _p**2  # the order of the field
    __Fp2_zero = _Fp2(0)  # the zero of the field
    __Fp2_one = _Fp2(1)  # the one of the field

    # curve parameters
    __curve_a = _Fp2([0, 0])  # the a coefficient of the curve
    __curve_b = _Fp2([3, 0]) / _Fp2([9, 1])  # the b coefficient of the curve
    __curve_order = _r  # the order of the curve

    def __init__(self, x: "tuple[int, int]", y: "tuple[int, int]", z=_Fp2(1), verify=True) -> None:
        if verify:
            x, y, z = map(self.__Fp2, (x, y, z))
            if not self.is_on_curve(x, y, z):
                raise ValueError(f"({x}, {y}, {z}) is not on G2")
        self.x = x
        self.y = y
        self.z = z
    
    @classmethod
    def is_on_curve(cls, x: "tuple[int, int]", y: "tuple[int, int]", z=_Fp2(1)) -> bool:
        x, y, z = map(cls.__Fp2, (x, y, z))
        # equivalent to (y / z^3)^2 == (x / z^2)^3 + b
        return y**2 == x**3 + cls.__curve_b * z**3
    
    @classmethod
    def order(cls) -> int:
        """ Return the order of G2 """
        return cls.__curve_order
    
    @classmethod
    def generator(cls) -> "G2":
        """ Return the generator of the group G2 """
        return G2(cls.__Fp2([
            10857046999023057135944570762232829481370756359578518086990519993285655852781,
            11559732032986387107991004021392285783925812861821192530917403151452391805634
        ]), cls.__Fp2([
            8495653923123431417604973247489272438418190587263600148770280649306958101930,
            4082367875863433681332203403145435568316851327593401208105741076214120093531
        ]), verify=False)
    
    @classmethod
    def zero(cls) -> "G2":
        """ Return the zero of G2 """
        return G2(cls.__Fp2_zero, cls.__Fp2_one, cls.__Fp2_zero, verify=False)
    
    def is_zero(self) -> bool:
        """ Return True if the point is the zero point """
        return self.z == self.__Fp2_zero
    
    def to_affine(self) -> None:
        """ Return the affine representation of the point """
        if self.z == self.__Fp2_zero:
            self.x = self.__Fp2_zero
            self.y = self.__Fp2_one
        else:
            z_inv = self.z**-1
            z_inv_squared = z_inv**2
            z_inv_cubed = z_inv * z_inv_squared
            self.x = self.x * z_inv_squared
            self.y = self.y * z_inv_cubed
            self.z = self.__Fp2_one
    
    def to_bytes(self) -> bytes:
        """ Return the bytes representation of the point """
        return bytes(self)
    
    @classmethod
    def from_bytes(cls, data: bytes) -> "G2":
        """ Return the point from the bytes representation """
        if not isinstance(data, bytes):
            raise TypeError(f"Invalid bytes representation type: {type(data)}")
        if len(data) != 64:
            raise ValueError(f"Invalid bytes representation length: {len(data)}, expected 64 bytes")
        
        r0, r1 = int.from_bytes(data[:32], "big"), int.from_bytes(data[32:], "big")
        if r0 == 0 and r1 == 0:
            return cls.zero()
        x = cls.__Fp2([r0 % 2**254, r1 % 2**254])
        try:
            y = (x**3 + cls.__curve_b).sqrt()
        except Exception:
            raise ValueError(f"Invalid bytes representation for G2: {hex(data)[2:].zfill(2 * cls.bytes_size)}")
        y_c0, y_c1 = map(int, y)
        if r0 // 2**254 - 2 == y_c0 & 1 and r1 // 2**254 - 2 == y_c1 & 1:
            return G2(x, y, verify=False)
        return G2(x, -y, verify=False)
    
    def __mul__(self, scalar: int) -> "G2":
        """ Return the scalar multiplication of the point """

        if getattr(scalar, "__int__", None) is None:
            raise TypeError(f"Multiplication is not defined for: G2 * {type(scalar)}")
        if not isinstance(scalar, int):
            scalar = int(scalar) % self.__curve_order
        
        # calls external function that does not use the class to make exponentiation faster
        x, y, z = map(self.__Fp2, _optimized_scalar_multiplication((self.x, self.y, self.z), scalar))
        return G2(x, y, z, verify=False)

    def __rmul__(self, scalar: int) -> "G2":
        """ Return the scalar multiplication of the point """

        if getattr(scalar, "__int__", None) is None:
            raise TypeError(f"Multiplication is not defined for: G2 * {type(scalar)}")
        if not isinstance(scalar, int):
            scalar = int(scalar) % self.__curve_order
        
        # calls external function that does not use the class to make exponentiation faster
        x, y, z = map(self.__Fp2, _optimized_scalar_multiplication((self.x, self.y, self.z), scalar))
        return G2(x, y, z, verify=False)
    
    def __add__(self, other: "G2") -> "G2":
        """ Return the addition of the two points """
        if not isinstance(other, G2):
            raise TypeError(f"Addition is not defined for: G2 + {type(other)}")
        
        if self.z == self.__Fp2_zero:
            return other
        if other.z == self.__Fp2_zero:
            return self
        
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl
        # self = (x1, y1, z1), other = (x2, y2, z2)

        z1_squared = self.z**2
        z2_squared = other.z**2

        u1 = self.x * z2_squared
        u2 = other.x * z1_squared

        z1_cubed = z1_squared * self.z
        z2_cubed = z2_squared * other.z

        s1 = self.y * z2_cubed
        s2 = other.y * z1_cubed

        if u1 == u2 and s1 == s2:
            return self.__double()
        
        h = u2 - u1
        i = (h + h)**2
        j = h * i
        r = s2 - s1
        r = r + r
        v = u1 * i

        x3 = r**2 - j - v - v
        s1_j = s1 * j
        y3 = r * (v - x3) - (s1_j + s1_j)
        z3 = ((self.z + other.z)**2 - z1_squared - z2_squared) * h

        return G2(x3, y3, z3, verify=False)
    
    def __double(self) -> "G2":
        """ Return the double of the point """
        if self.z == self.__Fp2_zero:
            return self
        
        # https://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
        # self = (x1, y1, z1)

        a = self.x**2
        b = self.y**2
        c = b**2
        d = (self.x + b)**2 - a - c
        d = d + d
        e = a + a + a
        f = e**2
        x3 = f - (d + d)
        _8c = c + c
        _8c = _8c + _8c
        _8c = _8c + _8c
        y3 = e * (d - x3) - _8c
        z3 = self.y * self.z
        z3 = z3 + z3

        return G2(x3, y3, z3, verify=False)
    
    def __neg__(self) -> "G2":
        """ Return the negation of the point """
        return G2(self.x, -self.y, self.z, verify=False)
    
    def __sub__(self, other: "G2") -> "G2":
        """ Return the subtraction of the two points """
        if not isinstance(other, G2):
            raise TypeError(f"Subtraction is not defined for: G2 - {type(other)}")
        return self.__add__(-other)
    
    def __eq__(self, other: "G2") -> bool:
        """ Return True if the points are equal """
        if not isinstance(other, G2):
            return False
        
        if self.z == self.__Fp2_zero:
            return other.z == self.__Fp2_zero
        if other.z == self.__Fp2_zero:
            return False
        
        z1_squared = self.z**2
        z2_squared = other.z**2

        if self.x * z2_squared != other.x * z1_squared:
            return False
        
        z1_cubed = z1_squared * self.z
        z2_cubed = z2_squared * other.z

        return self.y * z2_cubed == other.y * z1_cubed
    
    def __ne__(self, other: "G2") -> bool:
        """ Return True if the points are not equal """
        return not self.__eq__(other)
    
    def __repr__(self) -> str:
        """ Return the string representation of the point """
        self.to_affine()
        return f"G2({self.x}, {self.y})"
    
    def __str__(self) -> str:
        """ Return the string representation of the point """
        return self.__repr__()
    
    def __bytes__(self) -> bytes:
        """ Return the bytes representation of the point in compressed form """
        self.to_affine()
        if self.z == self.__Fp2_zero:
            return b"\x00" * 64
        x_c0, x_c1 = map(int, self.x)
        y_c0, y_c1 = map(int, self.y)
        return (((int(y_c0) & 1) + 2) * 2**254 + int(x_c0)).to_bytes(32, "big") + \
               (((int(y_c1) & 1) + 2) * 2**254 + int(x_c1)).to_bytes(32, "big")
    
    def __iter__(self) -> Iterable:
        return iter((self.x, self.y, self.z))


def __twist(p1: G2):
    """ Return the twist of the point (from G2 in Fp2 to G2 in Fp12) """
    # https://github.com/ethereum/py_ecc
    global _Fp2, _Fp12

    if not isinstance(p1, G2):
        raise TypeError(f"Twist is not defined for {type(p1)}, expected G2")

    x_c0, x_c1 = map(int, p1.x)
    y_c0, y_c1 = map(int, p1.y)
    z_c0, z_c1 = map(int, p1.z)

    x = _Fp12([x_c0 - 9 * x_c1] + [0] * 5 + [x_c1] + [0] * 5)
    y = _Fp12([y_c0 - 9 * y_c1] + [0] * 5 + [y_c1] + [0] * 5)
    z = _Fp12([z_c0 - 9 * z_c1] + [0] * 5 + [z_c1] + [0] * 5)

    w = _Fp12.gen()
    return (x * w**2, y * w**3, z)


# ---------------------------------------------
# Pairing Algorithms

# Taken from https://github.com/ethereum/py_ecc

__ate_loop_count = 29793968203157093288
__pseudo_binary_encoding = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0,
    0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1,
    1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1,
    1, 0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, 1, 1,
]
assert sum([e * 2**i for i, e in enumerate(__pseudo_binary_encoding)]) == __ate_loop_count


def __linefunc(p1: tuple, p2: tuple, t: tuple) -> tuple:
    # https://github.com/ethereum/py_ecc
    x1, y1, _ = p1
    x2, y2, _ = p2
    xt, yt, _ = t
    if x1 != x2:
        m = (y2 - y1) / (x2 - x1)
        return m * (xt - x1) - (yt - y1)
    elif y1 == y2:
        m = 3 * x1**2 / (2 * y1)
        return m * (xt - x1) - (yt - y1)
    else:
        return xt - x1


def __miller_loop(p1: tuple, p2: tuple, final_exponentiate=True) -> Any:
    # https://github.com/ethereum/py_ecc
    global _Fp12, __pseudo_binary_encoding, _p, _r
    neg = lambda x: (x[0], -x[1], x[2])
    
    p1, p2 = map(__to_affine, (p1, p2))
    r = p1
    p1_neg = neg(p1)

    f = _Fp12(1)
    for v in reversed(__pseudo_binary_encoding[:-1]):  # contains only {-1, 0, 1}
        f = f * f * __linefunc(r, r, p2)
        r = __to_affine(__double(r))
        if v == 1:
            f *= __linefunc(r, p1, p2)
            r = __to_affine(__affine_add(r, p1))
        if v == -1:
            f *= __linefunc(r, p1_neg, p2)
            r = __to_affine(__affine_add(r, p1_neg))
    # assert r == __to_affine(_optimized_scalar_multiplication(p1, __ate_loop_count))
    
    raise_to_p = lambda x: x**_p

    q1 = tuple(map(raise_to_p, p1))
    q2_neg = tuple(map(raise_to_p, neg(q1)))

    f *= __linefunc(r, q1, p2)
    r = __to_affine(__add(r, q1))
    f *= __linefunc(r, q2_neg, p2)
    # r = __to_affine(__add(r, q2_neg))  # useless
    
    return f**((_p**12 - 1) // _r) if final_exponentiate else f


def e(p1: G1, p2: G2) -> Any:
    """ Return the pairing of the two points of G1 and G2 """
    global _Fp12

    if not isinstance(p1, G1) or not isinstance(p2, G2):
        raise TypeError(f"Pairing is not defined for: {type(p1)} and {type(p2)}")
    
    if p1.z == 0 or p2.z == 0:
        return _Fp12(1)
    return __miller_loop(__twist(p2), tuple(map(_Fp12, p1)), final_exponentiate=True)


# Expose the following functions and classes
__all__ = ["G1", "G2", "e"]


if __name__ == "__main__":
    import time, random

    print("Testing the elliptic curve operations")
    g1 = G1.generator()
    g2 = G2.generator()
    assert g1 * G1.order() == G1.zero()
    assert g2 * G2.order() == G2.zero()

    print("Testing elliptic curve to and from bytes")
    x = random.randint(0, 2**256)
    p1 = x * g1
    p2 = x * g2
    assert p1 == G1.from_bytes(bytes(p1))
    assert p2 == G2.from_bytes(bytes(p2))

    print("Testing the pairing function")
    assert e(g1, g2) != 1
    a, b = random.randrange(1, G1.order()), random.randrange(1, G2.order())
    assert e(a * g1, b * g2) == e(g1, g2)**(a * b), f"{e(a * g1, b * g2)}\n{e(g1, g2)**(a * b)}"

    print("Testing the performance of the pairing function")
    start = time.time()
    e(random.randrange(1, G1.order()) * g1, random.randrange(1, G2.order()) * g2)
    print(f"Time: {time.time() - start:.3f} seconds")

    print("All tests passed")
