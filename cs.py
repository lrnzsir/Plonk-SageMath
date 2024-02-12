"""
This module provides a class for the definition of constraint systems for the Plonk proof system.

The available constraint systems are:
- evaluation_poly_of_degree: for the evaluation of an arbitrary polynomial of degree d at an arbitrary point.
- sha256_proof_of_work: for the proof of work of the SHA-256 hash function.
"""

from field import F, possible_subgroup_sizes


class ConstraintSystem:
    """
    A class for the definition of constraint systems for the Plonk proof system.

    The available constraint systems are:
    - evaluation_poly_of_degree: for the evaluation of an arbitrary polynomial of degree d at an arbitrary point.
    - sha256_proof_of_work: for the proof of work of the SHA-256 hash function.

    Also, the class provides methods for the computation of the witness from the public inputs (and data to compute the witness, e.g. the full data to be hashed for the SHA-256 proof of work).
    """

    def __init__(self) -> None:
        """ Do not instantiate directly """
        self.__is_correctly_defined = False
        self.name = "EmptyConstraintSystem"
        self.n = 0  # number of gates
        self.m = 0  # count of wires
        self._gate_names = []  # list of strings
        self._gates = []  # list of tuples of elements of F (qL, qR, qO, qM, qC)
        self._wires = []  # list of tuples of indices (left, right, output)
        self._sigma = []  # permutation of the wires (will be computed at the end of the construction)
        self._wire_index_to_sigma_index = []  # map from wire index to sigma index (will be computed at the end of the construction)
    
    def is_correctly_defined(self) -> bool:
        return self.__is_correctly_defined
    
    def __get_new_wires(self, n: int) -> "list[int]":
        """ Return a list of n new wires. """
        wires = list(range(self.m, self.m + n))
        self.m += n
        return wires
    
    def __custom_gate(self, gate_name: str, gate: "tuple[int, int, int, int, int]", wires: "tuple[int, int, int]") -> None:
        self._gate_names.append(gate_name)
        self._gates.append(gate)
        self._wires.append(wires)

    def __public_input(self, a: int) -> None:
        self._gate_names.append("public_input")
        self._gates.append((1, 0, 0, 0, 0))
        self._wires.append((a, None, None))

    def __enforce_value(self, a: int, value: int) -> None:
        self._gate_names.append("enforce_value")
        self._gates.append((1, 0, 0, 0, -value))
        self._wires.append((a, None, None))
    
    def __enforce_value_witness(self, w: "list[int]", a: int, value: int) -> "list[int]":
        if w[a] is not None and w[a] != value:
            raise ValueError(f"Invalid witness for the value enforcement: [{a}] = {w[a]}")
        return self.__popolate_witness_with_sigma(w, a, value)

    def __equality(self, a: int, b: int) -> None:
        self._gate_names.append("equality")
        self._gates.append((1, 0, -1, 0, 0))
        self._wires.append((a, None, b))

    def __equality_witness(self, w: "list[int]", a: int, b: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[a] != w[b]:
            raise ValueError(f"Invalid witness for the equality gate: [{a}] = {w[a]} != {w[b]} = [{b}]")
        if w[a] is not None and w[b] is None:
            return self.__popolate_witness_with_sigma(w, b, w[a])
        if w[a] is None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, a, w[b])
        return w

    def __addition(self, a: int, b: int, c: int) -> None:
        self._gate_names.append("addition")
        self._gates.append((1, 1, -1, 0, 0))
        self._wires.append((a, b, c))
    
    def __addition_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if w[a] + w[b] != w[c]:
                raise ValueError(f"Invalid witness for the addition gate: [{a}] + [{b}] = [{c}]")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, w[a] + w[b])
        elif w[a] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, b, w[c] - w[a])
        elif w[b] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, a, w[c] - w[b])
        return w
        
    def __multiplication(self, a: int, b: int, c: int) -> None:
        self._gate_names.append("multiplication")
        self._gates.append((0, 0, -1, 1, 0))
        self._wires.append((a, b, c))
    
    def __multiplication_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if w[a] * w[b] != w[c]:
                raise ValueError(f"Invalid witness for the multiplication gate: [{a}] * [{b}] = [{c}]")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, w[a] * w[b])
        elif w[a] is not None and w[c] is not None:
            if w[a] == 0:
                return w
            return self.__popolate_witness_with_sigma(w, b, w[c] / w[a])
        elif w[b] is not None and w[c] is not None:
            if w[b] == 0:
                return w
            return self.__popolate_witness_with_sigma(w, a, w[c] / w[b])
        return w
    
    def __booleanity(self, a: int) -> None:
        self._gate_names.append("booleanity")
        self._gates.append((-1, 0, 0, 1, 0))
        self._wires.append((a, a, None))    
    
    def __bool_not(self, a: int, b: int) -> None:
        self._gate_names.append("bool_not")
        self._gates.append((-1, 0, -1, 0, 1))
        self._wires.append((a, None, b))
    
    def __bool_not_witness(self, w: "list[int]", a: int, b: int) -> "list[int]":
        if w[a] is not None and w[b] is not None:
            if w[a] == 1 - w[b]:
                return w
            raise ValueError(f"Invalid witness for the not gate: [{a}] - 1 + [{b}] = 0")

        if w[a] is not None:
            return self.__popolate_witness_with_sigma(w, b, 1 - w[a])
        if w[b] is not None:
            return self.__popolate_witness_with_sigma(w, a, 1 - w[b])
        return w

    def __bool_and(self, a: int, b: int, c: int) -> None:
        self._gate_names.append("bool_and")
        self._gates.append((0, 0, -1, 1, 0))
        self._wires.append((a, b, c))
    
    def __bool_and_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if w[a] * w[b] != w[c]:
                raise ValueError(f"Invalid witness for the and gate: [{a}] * [{b}] = [{c}]")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, w[a] * w[b])
        elif w[a] is not None and w[c] is not None and w[a] == 1:
            return self.__popolate_witness_with_sigma(w, b, w[c])
        elif w[b] is not None and w[c] is not None and w[b] == 1:
            return self.__popolate_witness_with_sigma(w, a, w[c])
        return w

    def __bool_or(self, a: int, b: int, c: int) -> None:
        # 0 0 0 | 0 + 0 - 0 - 0 * 0 = 0
        # 1 0 1 | 1 + 0 - 1 - 1 * 0 = 0
        # 0 1 1 | 0 + 1 - 1 - 0 * 1 = 0
        # 1 1 1 | 1 + 1 - 1 - 1 * 1 = 0
        self._gate_names.append("bool_or")
        self._gates.append((1, 1, -1, -1, 0))
        self._wires.append((a, b, c))
    
    def __bool_or_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if w[a] + w[b] - w[c] - w[a] * w[b] != 0:
                raise ValueError(f"Invalid witness for the or gate: [{a}] + [{b}] - [{c}] - [{a}] * [{b}] = 0")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, w[a] + w[b] - w[a] * w[b])
        if w[a] is not None and w[c] is not None and w[a] == 0:
            return self.__popolate_witness_with_sigma(w, b, w[c])
        if w[b] is not None and w[c] is not None and w[b] == 0:
            return self.__popolate_witness_with_sigma(w, a, w[c])
        return w
    
    def __bool_xor(self, a: int, b: int, c: int) -> None:
        # 0 0 0 | 0 + 0 - 0 - 2 * 0 * 0 = 0
        # 1 0 1 | 1 + 0 - 1 - 2 * 1 * 0 = 0
        # 0 1 1 | 0 + 1 - 1 - 2 * 0 * 1 = 0
        # 1 1 0 | 1 + 1 - 0 - 2 * 1 * 1 = 0
        self._gate_names.append("bool_xor")
        self._gates.append((1, 1, -1, -2, 0))
        self._wires.append((a, b, c))
    
    def __bool_xor_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if w[a] + w[b] - w[c] - 2 * w[a] * w[b] != 0:
                raise ValueError(f"Invalid witness for the xor gate: [{a}] + [{b}] - [{c}] - 2 * [{a}] * [{b}] = 0")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, w[a] + w[b] - 2 * w[a] * w[b])
        if w[a] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, b, F(int(w[a]) ^ int(w[c])))
        if w[b] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, a, F(int(w[b]) ^ int(w[c])))
        return w

    def __double_left_add_right(self, a: int, b: int, c: int) -> None:
        self._gate_names.append("double_left_add_right")
        self._gates.append((2, 1, -1, 0, 0))
        self._wires.append((a, b, c))
    
    def __double_left_add_right_witness(self, w: "list[int]", a: int, b: int, c: int) -> "list[int]":
        if w[a] is not None and w[b] is not None and w[c] is not None:
            if 2 * w[a] + w[b] != w[c]:
                raise ValueError(f"Invalid witness for the double left add right gate: 2 * [{a}] + [{b}] = [{c}]")

        if w[a] is not None and w[b] is not None:
            return self.__popolate_witness_with_sigma(w, c, 2 * w[a] + w[b])
        elif w[a] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, b, w[c] - 2 * w[a])
        elif w[b] is not None and w[c] is not None:
            return self.__popolate_witness_with_sigma(w, a, w[c] - w[b])
        return w

    def __byte_to_bits(self, a: int, bs: "list[int]") -> None:
        # b1, ..., b8 = bs (from the most significant to the least significant bit)
        # b1 * 2 + b2
        # (b1 * 2 + b2) * 2 + b3
        # ...
        # a
        if len(bs) != 8:
            raise ValueError("The list of bits must have length 8")
        
        res = self.m
        self.m += 1
        self.__double_left_add_right(bs[0], bs[1], res)
        for b in bs[2:-1]:
            self.__double_left_add_right(res, b, res + 1)
            res += 1
            self.m += 1
        self.__double_left_add_right(res, bs[-1], a)
    
    def __addition_bit_by_bit(self, as_: "list[int]", bs: "list[int]", cs: "list[int]") -> None:
        # a1, ..., an = as_ (from the most significant to the least significant bit)
        if len(as_) != len(bs) or len(bs) != len(cs):
            raise ValueError("The lists of bits must have the same length")
        # reverse the lists to start from the least significant bit
        as_, bs, cs = as_[::-1], bs[::-1], cs[::-1]
        
        # least significant bit
        carry = self.__get_new_wires(1).pop()
        self.__bool_xor(as_[0], bs[0], cs[0])
        self.__bool_and(as_[0], bs[0], carry)

        # intermediate bits
        for a, b, c in zip(as_[1:-1], bs[1:-1], cs[1:-1]):
            # take new wires for the intermediate results
            old_carry = carry
            res_xor, res_and1, res_and2, carry = self.__get_new_wires(4)
            # compute the value of the sum
            self.__bool_xor(a, b, res_xor)
            self.__bool_xor(res_xor, old_carry, c)
            # compute the value of the carry
            self.__bool_and(a, b, res_and1)
            self.__bool_and(res_xor, old_carry, res_and2)
            self.__bool_or(res_and1, res_and2, carry)
        
        # most significant bit
        old_carry = carry
        res_xor = self.__get_new_wires(1).pop()
        self.__bool_xor(as_[-1], bs[-1], res_xor)
        self.__bool_xor(res_xor, old_carry, cs[-1])
    
    def __addition_bit_by_bit_constant(self, as_: "list[int]", b: int) -> "list[int]":
        # a1, ..., an = as_ (from the most significant to the least significant bit)
        # b is a constant int of n bits
        
        # reverse the list to start from the least significant bit
        as_ = as_[::-1]
        cs = []
        
        # skip the least significant bits of b if they are 0
        for i in range(len(as_)):
            if b & 1:
                break
            b >>= 1
            cs.append(as_[i])

        # least significant bit set to 1
        cs.append(self.m)
        carry = as_[i]
        self.m += 1
        self.__bool_not(as_[i], cs[i])
        b >>= 1

        # intermediate bits
        for j in range(i + 1, len(as_) - 1):
            if b & 1:
                # take new wires for the intermediate results
                old_carry = carry
                cs.append(self.m)
                res_xor = self.m + 1
                carry = self.m + 2
                self.m += 3
                # compute the value of the sum
                self.__bool_not(as_[j], res_xor)
                self.__bool_xor(res_xor, old_carry, cs[j])
                # compute the value of the carry
                # a b carry | new carry
                # 0 1 0     | 0
                # 1 1 0     | 1
                # 0 1 1     | 1
                # 1 1 1     | 1
                self.__bool_or(as_[j], old_carry, carry)
            else:
                # take new wires for the intermediate results
                old_carry = carry
                cs.append(self.m)
                carry = self.m + 1
                self.m += 2
                # compute the value of the sum
                self.__bool_xor(as_[j], old_carry, cs[j])
                # compute the value of the carry
                self.__bool_and(as_[j], old_carry, carry)
            b >>= 1
        
        # most significant bit
        if b & 1:
            old_carry = carry
            cs.append(self.m)
            res_xor = self.m + 1
            self.m += 2
            self.__bool_not(as_[-1], res_xor)
            self.__bool_xor(res_xor, old_carry, cs[-1])
        else:
            old_carry = carry
            cs.append(self.m)
            self.m += 1
            self.__bool_xor(as_[-1], old_carry, cs[-1])
        
        # return the list of wires representing the sum in the correct order
        return cs[::-1]
    
    def __not_bit_by_bit(self, as_: "list[int]", bs: "list[int]") -> None:
        if len(as_) != len(bs):
            raise ValueError("The lists of bits must have the same length")
        
        for a, b in zip(as_, bs):
            self.__bool_not(a, b)
    
    def __and_bit_by_bit(self, as_: "list[int]", bs: "list[int]", cs: "list[int]") -> None:
        if len(as_) != len(bs) or len(bs) != len(cs):
            raise ValueError("The lists of bits must have the same length")
        
        for a, b, c in zip(as_, bs, cs):
            self.__bool_and(a, b, c)
    
    def __or_bit_by_bit(self, as_: "list[int]", bs: "list[int]", cs: "list[int]") -> None:
        if len(as_) != len(bs) or len(bs) != len(cs):
            raise ValueError("The lists of bits must have the same length")
        
        for a, b, c in zip(as_, bs, cs):
            self.__bool_or(a, b, c)

    def __xor_bit_by_bit(self, as_: "list[int]", bs: "list[int]", cs: "list[int]") -> None:
        if len(as_) != len(bs) or len(bs) != len(cs):
            raise ValueError("The lists of bits must have the same length")
        
        for a, b, c in zip(as_, bs, cs):
            self.__bool_xor(a, b, c)

    def __sigma(self) -> None:
        # concatenate the padded lists of left, right and output indices

        for i, name, (a, b, c) in zip(range(len(self._gates)), self._gate_names, self._wires):
            if a is not None:
                if a >= self.m:
                    raise ValueError(f"Invalid wire index {a} in the {i}-th gate {name} (m = {self.m})")
            if b is not None:
                if b >= self.m:
                    raise ValueError(f"Invalid wire index {b} in the {i}-th gate {name} (m = {self.m})")
            if c is not None:
                if c >= self.m:
                    raise ValueError(f"Invalid wire index {c} in the {i}-th gate {name} (m = {self.m})")

        import itertools
        concat = list(itertools.chain.from_iterable(
            map(lambda x: x + [None] * (self.n - len(x)), map(list, zip(*self._wires)))
        ))
        
        # compute the permutation sigma
        self._sigma = [None] * 3 * self.n
        self._wire_index_to_sigma_index = [None] * self.m
        prev_idx = [None] * self.m
        for i, idx in enumerate(concat):
            if idx is None:
                continue
            if idx >= self.m:
                raise ValueError(f"Invalid wire index {idx} at position {i} of the permutation (m = {self.m})")
            if prev_idx[idx] is None:  # first occurrence of the index
                prev_idx[idx] = i
                self._wire_index_to_sigma_index[idx] = i  # map the first occurrence of the index to its position in the permutation
                continue
            self._sigma[i] = prev_idx[idx]
            prev_idx[idx] = i
        
        # complete the permutation sigma
        for i in range(self.m):
            if prev_idx[i] is None:
                continue
            self._sigma[self._wire_index_to_sigma_index[i]] = prev_idx[i]
        for i in range(3 * self.n):
            if self._sigma[i] is None:
                self._sigma[i] = i

        # check that the permutation is well defined
        count_wires = [0] * self.m
        for x in concat:
            if x is not None:
                count_wires[x] += 1
        sigma_domain = [i for i, x in enumerate(concat) if x is not None and count_wires[x] > 0]
        assert all(self._sigma[i] is not None for i in sigma_domain), f"The permutation of the wires is not well defined"
        unused_wires = [i for i, x in enumerate(self._wire_index_to_sigma_index) if x is None]
        assert len(unused_wires) == 0, f"Some wires are not in the computation of {self.__name}"
    
    def __popolate_witness_with_sigma(self, w: "list[int]", i: int, v: int) -> "list[int]":
        """ Popolate the witness with the value v at the positions of the orbit of i in the permutation sigma. """
        if w[i] is not None:
            return w
        w[i] = F(v)
        j = self._sigma[i]
        while j != i:
            w[j] = F(v)
            j = self._sigma[j]
        return w
            
    @staticmethod
    def evaluation_poly_of_degree(d: int) -> "ConstraintSystem":
        """
        Return a constraint system for the evaluation of a arbitrary polynomial of degree d at an arbitrary point.
        
        The public inputs are arranged as follows:
        - the first wire encodes the X value;
        - the next d + 1 wires encode the coefficients of the polynomial.
        """
        cs = ConstraintSystem()

        ngates = 3 * (d + 1) + 3  # number of gates at the end of the construction
        for size in possible_subgroup_sizes:
            if size >= ngates:
                cs.n = size
                break
        else:
            raise ValueError(f"The degree {d} is too high, no multiplicative subgroup of order >= {ngates} found")
        
        cs.__d = d  # exclusive attribute for this constraint system
        cs.__name = f"Evaluation-Poly-Of-Degree"
        cs.name = cs.__name + f"-{d}"

        # public inputs
        X = cs.__get_new_wires(1).pop()  # index of the wire representing X
        coeffs = cs.__get_new_wires(d + 1)  # index of the wires representing the coefficients

        # witness
        res = cs.__get_new_wires(1).pop()  # index of the wire representing the result of the polynomial evaluation
        
        # prepare the gates for the public inputs
        cs.__public_input(X)
        for coeff in coeffs:
            cs.__public_input(coeff)
        
        # polynomial evaluation
        cs.__enforce_value(cs.m, 0)
        for coeff in reversed(coeffs):
            cs.__multiplication(X, cs.m, cs.m + 1)
            cs.__addition(coeff, cs.m + 1, cs.m + 2)
            cs.m += 2
        
        # enforce that the result is equal to the polynomial evaluation
        cs.__equality(cs.m, res)
        cs.m += 1

        # compute the permutation of the wires
        cs.__sigma()

        cs.__is_correctly_defined = True
        return cs

    def __compute_witness_evaluation_poly_of_degree(self, public_inputs: "list[int]") -> "list[int]":
        """ Compute the witness from the public inputs for the evaluation of a polynomial of degree d. """
        
        if len(public_inputs) != self.__d + 2:
            raise ValueError(f"Expected {self.__d + 2} public inputs, got {len(public_inputs)} (first input is the X value, the next {self.__d + 1} inputs are the coefficients)")
        
        # cast the public inputs to the field F
        x = F(public_inputs[0])
        coeffs = list(map(F, public_inputs[1:]))
        
        wire_values = []
        res = 0
        wire_values.append(res)
        for c in reversed(coeffs):
            res *= x
            wire_values.append(res)
            res += c
            wire_values.append(res)
        wire_values = [x] + coeffs + [res] + wire_values

        witness = [0] * 3 * self.n
        for i, v in enumerate(wire_values):
            i = self._wire_index_to_sigma_index[i]
            witness[i] = v
            j = self._sigma[i]
            while j != i:
                witness[j] = v
                j = self._sigma[j]
        
        return [x if x is not None else F.random_element() for x in witness]
    
    def __sha256_extend(self, w: "list[list[int]]") -> None:
        """ Extend the message schedule array for the SHA-256 hash function. """

        right_rotate = lambda x, n: x[-n:] + x[:-n]
        right_shift = lambda x, n: x[:-n]

        for i in range(16, 64):
            # first xor of s0
            as_, bs = right_rotate(w[i - 15], 7), right_rotate(w[i - 15], 18)
            cs = self.__get_new_wires(32)
            self.__xor_bit_by_bit(as_, bs, cs)
            # second xor of s0
            as_, bs = cs, right_shift(w[i - 15], 3)
            cs = as_[:3] + self.__get_new_wires(32 - 3)
            self.__xor_bit_by_bit(as_[3:], bs, cs[3:])
            # result of s0
            s0 = cs

            # first xor of s1
            as_, bs = right_rotate(w[i - 2], 17), right_rotate(w[i - 2], 19)
            cs = self.__get_new_wires(32)
            self.__xor_bit_by_bit(as_, bs, cs)
            # second xor of s1
            as_, bs = cs, right_shift(w[i - 2], 10)
            cs = as_[:10] + self.__get_new_wires(32 - 10)
            self.__xor_bit_by_bit(as_[10:], bs, cs[10:])
            # result of s1
            s1 = cs

            # sum of the results
            r1 = self.__get_new_wires(32)
            r2 = self.__get_new_wires(32)
            self.__addition_bit_by_bit(w[i - 16], s0, r1)
            self.__addition_bit_by_bit(w[i - 7], s1, r2)
            self.__addition_bit_by_bit(r1, r2, w[i])
    
    def __sha256_compress(self, hash: "list[list[int]]", w: "list[list[int]]") -> "list[int]":
        """ Return the list of wires representing the SHA-256 compression function result. """

        right_rotate = lambda x, n: x[-n:] + x[:-n]

        # round constants
        k = (
            0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
            0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
            0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
            0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
            0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
            0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
            0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
            0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
        )

        def compute_S1(e: "list[int]") -> "list[int]":
            S1 = self.__get_new_wires(32)
            res = self.__get_new_wires(32)
            self.__xor_bit_by_bit(right_rotate(e, 6), right_rotate(e, 11), res)
            self.__xor_bit_by_bit(res, right_rotate(e, 25), S1)
            return S1

        def compute_ch(e: "list[int]", f: "list[int]", g: "list[int]") -> "list[int]":
            ch = self.__get_new_wires(32)
            not_e = self.__get_new_wires(32)
            res_and1 = self.__get_new_wires(32)
            res_and2 = self.__get_new_wires(32)
            self.__and_bit_by_bit(e, f, res_and1)
            self.__not_bit_by_bit(e, not_e)
            self.__and_bit_by_bit(not_e, g, res_and2)
            self.__xor_bit_by_bit(res_and1, res_and2, ch)
            return ch
        
        def compute_temp1(h: "list[int]", S1: "list[int]", ch: "list[int]", k: int, w: "list[int]") -> "list[int]":
            temp1 = self.__get_new_wires(32)
            res_add1 = self.__addition_bit_by_bit_constant(h, k)
            res_add2 = self.__get_new_wires(32)
            res_add3 = self.__get_new_wires(32)
            self.__addition_bit_by_bit(res_add1, S1, res_add2)
            self.__addition_bit_by_bit(res_add2, ch, res_add3)
            self.__addition_bit_by_bit(w, res_add3, temp1)
            return temp1

        def compute_S0(a: "list[int]") -> "list[int]":
            S0 = self.__get_new_wires(32)
            res = self.__get_new_wires(32)
            self.__xor_bit_by_bit(right_rotate(a, 2), right_rotate(a, 13), res)
            self.__xor_bit_by_bit(res, right_rotate(a, 22), S0)
            return S0
        
        def compute_maj(a: "list[int]", b: "list[int]", c: "list[int]") -> "list[int]":
            maj = self.__get_new_wires(32)
            res_and1 = self.__get_new_wires(32)
            res_and2 = self.__get_new_wires(32)
            res_and3 = self.__get_new_wires(32)
            res = self.__get_new_wires(32)
            self.__and_bit_by_bit(a, b, res_and1)
            self.__and_bit_by_bit(a, c, res_and2)
            self.__and_bit_by_bit(b, c, res_and3)
            self.__xor_bit_by_bit(res_and1, res_and2, res)
            self.__xor_bit_by_bit(res, res_and3, maj)
            return maj
        
        def compute_temp2(S0: "list[int]", maj: "list[int]") -> "list[int]":
            temp2 = self.__get_new_wires(32)
            self.__addition_bit_by_bit(S0, maj, temp2)
            return temp2

        # initial hash values
        a, b, c, d, e, f, g, h = hash
        
        # rounds of the SHA-256 compression function
        for i in range(64):
            # compute the S1, ch, temp1, S0, maj and temp2 values
            S1 = compute_S1(e)
            ch = compute_ch(e, f, g)
            temp1 = compute_temp1(h, S1, ch, k[i], w[i])
            S0 = compute_S0(a)
            maj = compute_maj(a, b, c)
            temp2 = compute_temp2(S0, maj)
            # update the values of a, b, c, d, e, f, g, h
            h, g, f = g, f, e
            e = self.__get_new_wires(32)
            self.__addition_bit_by_bit(temp1, d, e)
            d, c, b = c, b, a
            a = self.__get_new_wires(32)
            self.__addition_bit_by_bit(temp1, temp2, a)
        
        return [a, b, c, d, e, f, g, h]

    def __sha256(self, data: "list[int]", hash_out: "list[int]") -> None:
        """ Compute the SHA-256 hash of the given data wires (bits) and set the hash to the given hash_out wires (bits) """
        
        # ----------------------------------------
        # Constants

        # initial hash values
        hash = (0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19)

        # convert the initial hash values to bits and set them
        hash_bits_values = [list(map(int, bin(h)[2:].zfill(32))) for h in hash]
        hash_bits = self.__get_new_wires(32 * 8)
        hash_bits = [hash_bits[i:i + 32] for i in range(0, 32 * 8, 32)]
        for i in range(8):
            for j in range(32):
                self.__enforce_value(hash_bits[i][j], hash_bits_values[i][j])

        # ----------------------------------------
        # Preprocessing

        # index of the wires representing the chunk (512 bits)
        chunk = data + self.__get_new_wires(512 - len(data))

        # make sure that the chunk values are bits
        for i in chunk[len(data):]:
            self.__booleanity(i)

        # pad the chunk
        self.__enforce_value(chunk[len(data)], 1)
        for i in range(len(data) + 1, 512 - 64):
            self.__enforce_value(chunk[i], 0)
        
        # set the length of the data
        for i, v in enumerate(map(int, bin(len(data))[2:].zfill(64))):
            self.__enforce_value(chunk[512 - 64 + i], v)
        
        # ----------------------------------------
        # Extend and compress
            
        w = chunk + self.__get_new_wires(64 * 32 - len(chunk))  # message schedule
        w = [w[i:i + 32] for i in range(0, 64 * 32, 32)]

        # extend and compress the chunk
        self.__sha256_extend(w)
        compressed_chunk = self.__sha256_compress(hash_bits, w)

        # ----------------------------------------
        # Final hash

        hash_old = hash
        hash = []
        for i in range(8):
            hash.append(self.__addition_bit_by_bit_constant(compressed_chunk[i], hash_old[i]))
        
        import itertools
        hash = list(itertools.chain.from_iterable(hash))

        # set the hash to the output wires
        for i in range(32 * 8):
            self.__equality(hash_out[i], hash[i])
    
    @staticmethod
    def sha256_proof_of_work(seed_length: int, target_length: int, data_length: int) -> "ConstraintSystem":
        """
        Return a constraint system for the proof of work of the SHA-256 hash function with a given seed and target, i.e. prefix of the data to be hashed and prefix of the hash respectively.
        The length of the bytes to be hashed is given by the data_length parameter and must be less than or equal to 55 since we can perform only one round of the SHA-256 compression function.
        
        Regarding the creation of a witness with the compute_witness() method:
        - the public_inputs list is arranged as follows:
            - the first seed_length wires encode the first seed_length bytes to be hashed;
            - the next target_length wires encode the first target_length bytes of the target hash.
        - the witness_data dictionary must contain the full data to be hashed with the key "data".
        """
        if seed_length < 0:
            raise ValueError("The seed length must be non-negative")
        if target_length < 0:
            raise ValueError("The target length must be non-negative")
        if data_length < 0:
            raise ValueError("The data length must be non-negative")
        if seed_length > data_length:  # seed is a prefix of the data
            raise ValueError("The seed length must be less than or equal to the data length")
        if target_length > 32:  # the sha256 hash is 32 bytes long
            raise ValueError("The target length must be less than or equal to 32")
        if target_length > 64 - 1 - 8:  # the sha256 block is 64 bytes long, at least 1 byte is needed for padding and 8 bytes for the length
            raise ValueError("The data length must be less than or equal to 55")

        cs = ConstraintSystem()

        cs.__seed_length = seed_length  # exclusive attribute for this constraint system
        cs.__target_length = target_length  # exclusive attribute for this constraint system
        cs.__name = "SHA-256-Proof-Of-Work"
        cs.name = cs.__name + f"-{seed_length}-{target_length}-{data_length}"

        # public inputs
        seed = cs.__get_new_wires(seed_length)  # index of the wires representing the data
        target = cs.__get_new_wires(target_length)  # index of the wires representing the target hash

        # full data to be hashed
        data = seed + cs.__get_new_wires(data_length - seed_length)  # index of the wires representing the data

        # wires that represent the bits of the data to be hashed
        data_bits = cs.__get_new_wires(8 * data_length)

        # wires that represent the bits of the hash
        hash = cs.__get_new_wires(32 * 8)

        # prepare the gates for the public inputs
        for i in seed:
            cs.__public_input(i)
        for i in target:
            cs.__public_input(i)

        # make sure that the data values are bits
        for i in data_bits:
            cs.__booleanity(i)

        # set the data to the bits
        for i in range(data_length):
            cs.__byte_to_bits(data[i], data_bits[8 * i: 8 * (i + 1)])
        
        # enforce that the part of the hash corresponding to the target is the same as the target
        for i in range(target_length):
            cs.__byte_to_bits(target[i], hash[8 * i: 8 * (i + 1)])
        
        # hash the data
        cs.__sha256(data_bits, hash)
        
        # get the number of gates
        for size in possible_subgroup_sizes:  # TODO: move this at the beginning of the function when the number of gates will be known in advance
            if size >= len(cs._gates):
                cs.n = size
                break
        else:
            raise ValueError(f"No multiplicative subgroup of order >= {len(cs._gates)} found in SHA-256-Proof-Of-Work")
        
        # compute the permutation of the wires
        cs.__sigma()

        cs.__is_correctly_defined = True
        return cs
    
    def __compute_witness_sha256_proof_of_work(self, public_inputs: "list[int]", witness_data: "dict[str, int | list[int]]") -> "list[int]":
        """ Compute the witness from the public inputs for the proof of work of the SHA-256 hash function. """
        
        if len(public_inputs) != self.__seed_length + self.__target_length:
            raise ValueError(f"Expected {self.__seed_length + self.__target_length} public inputs, got {len(public_inputs)} (first {self.__seed_length} inputs are the seed, the next {self.__target_length} inputs are the target)")
        if "data" not in witness_data:
            raise ValueError('The full data to be hashed must be provided to compute the witness (key "data" of the witness data dictionary)')
        
        # cast the public inputs to the field F
        seed = list(map(F, public_inputs[:self.__seed_length]))
        target = list(map(F, public_inputs[self.__seed_length:self.__seed_length + self.__target_length]))
        data = list(map(F, witness_data["data"]))

        if len(seed) > len(data):
            raise ValueError("The seed is longer than the data")
        if any(x != y for x, y in zip(seed, data)):
            raise ValueError("The seed is not a prefix of the data")

        witness = [None] * 3 * self.n
        w2w = lambda i: self._wire_index_to_sigma_index[i]

        import itertools
        data_bits = list(itertools.chain.from_iterable(map(lambda x: map(F, bin(x)[2:].zfill(8)), data)))
        target_bits = list(itertools.chain.from_iterable(map(lambda x: map(F, bin(x)[2:].zfill(8)), target)))
        
        # set the public_inputs, the data bytes, the data bits and the hash bits
        for i, v in enumerate(seed + target + data[len(seed):] + data_bits + target_bits):
            witness = self.__popolate_witness_with_sigma(witness, w2w(i), v)
        
        # compute the witness
        for i, (qL, qR, qO, qM, qC), (a, b, c), name in zip(range(self.n), self._gates, self._wires, self._gate_names):
            if name == "public_input":
                continue
            elif name == "booleanity":
                continue
            elif name == "equality":
                witness = self.__equality_witness(witness, w2w(a), w2w(c))
            elif name == "enforce_value":
                witness = self.__enforce_value_witness(witness, w2w(a), F(-qC))
            elif name == "bool_not":
                witness = self.__bool_not_witness(witness, w2w(a), w2w(c))
            elif name == "bool_and":
                witness = self.__bool_and_witness(witness, w2w(a), w2w(b), w2w(c))
            elif name == "bool_or":
                witness = self.__bool_or_witness(witness, w2w(a), w2w(b), w2w(c))
            elif name == "bool_xor":
                witness = self.__bool_xor_witness(witness, w2w(a), w2w(b), w2w(c))
            elif name == "double_left_add_right":
                witness = self.__double_left_add_right_witness(witness, w2w(a), w2w(b), w2w(c))
            else:
                raise RuntimeError(f"Gate {name} not implemented in the computation of the witness for the SHA-256-Proof-Of-Work constraint system")
        
        return [x if x is not None else F.random_element() for x in witness]
    
    def compute_witness(self, public_inputs: "list[int]", witness_data=dict()) -> "list[int]":
        """
        Compute the witness from the public inputs of the constraint system. witness_data is a dictionary containing the data to be used in the computation depending on the constraint system. 
        
        Refer to the documentation of the specific constraint system for the expected format of the public inputs and the witness data.
        """
        if not self.__is_correctly_defined:
            raise ValueError("The constraint system is not correctly defined")
        
        if self.__name == "Evaluation-Poly-Of-Degree":
            return self.__compute_witness_evaluation_poly_of_degree(public_inputs)
        if self.__name == "SHA-256-Proof-Of-Work":
            return self.__compute_witness_sha256_proof_of_work(public_inputs, witness_data)
        return []  # if this happens there is a bug in the code, so we should not raise an exception
    
    def is_valid_witness(self, public_inputs: "list[int]", witness: "list[int]") -> bool:
        """ Check if the witness is valid for the constraint system and the public inputs. """
        if not self.__is_correctly_defined:
            raise ValueError("The constraint system is not correctly defined")
        
        # check that the witness is of the correct length
        if len(witness) != 3 * self.n:
            return False
        witness = list(map(F, witness))

        # check that the witness satisfies the public inputs
        if any(x != y for x, y in zip(public_inputs, witness)):
            return False
        
        # check that the witness satisfies the permutation sigma
        for i in self._wire_index_to_sigma_index:
            if i is None:
                continue
            v = witness[i]
            j = self._sigma[i]
            while j != i:
                if witness[j] != v:
                    return False
                j = self._sigma[j]

        # check that the witness satisfies the gates
        val = lambda i: witness[self._wire_index_to_sigma_index[i]] if i is not None else 0
        gates = list(map(lambda x: tuple(map(F, x)), self._gates))
        for i, (qL, qR, qO, qM, qC), (a, b, c) in zip(range(self.n), gates, self._wires):
            if qL * val(a) + qR * val(b) + qO * val(c) + qM * val(a) * val(b) + qC + (-public_inputs[i] if i < len(public_inputs) else 0) != 0:
                return False
        
        return True  # the witness is valid


__all__ = ["ConstraintSystem"]


if __name__ == "__main__":
    import hashlib, secrets

    print("Testing the ConstraintSystem class...")
    
    d = 3

    print(f"Testing the constraint system for the evaluation of a polynomial of degree {d}...")
    cs = ConstraintSystem.evaluation_poly_of_degree(d)
    assert cs.is_correctly_defined()
    
    x = F.random_element()
    coeffs = [F.random_element() for _ in range(d + 1)]
    public_inputs = [x] + coeffs

    witness = cs.compute_witness(public_inputs)
    assert cs.is_valid_witness(public_inputs, witness)

    print("Test passed!")

    print(f"Testing the constraint system for the proof of work of the SHA-256 hash function...")

    seed_length = 6
    target_length = 3
    data_length = 32

    cs = ConstraintSystem.sha256_proof_of_work(seed_length, target_length, data_length)
    
    seed = secrets.token_bytes(seed_length)
    data = seed + secrets.token_bytes(data_length - seed_length)
    target = hashlib.sha256(data).digest()[:target_length]

    witness = cs.compute_witness(list(seed) + list(target), {"data": list(data)})
    assert cs.is_valid_witness(list(seed) + list(target), witness)

    # test the non-validity of the witness
    for _ in range(10):
        i = secrets.randbelow(3 * cs.n)
        # the following could be False since the witness constains unused elements in the computation
        if not cs.is_valid_witness(list(seed) + list(target), witness[:i] + [F.random_element()] + witness[i + 1:]):
            break
    else:
        raise RuntimeError("The witness is always valid")

    print("Test passed!")

    print("All tests passed successfully for the ConstraintSystem class!")
