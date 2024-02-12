"""
Module for finite field arithmetic over the field F = GF(p), where p is the order of the elliptic curve bn128.

The module also provides a method to interpolate a polynomial via DFT (Discrete Fourier Transform)
from its evaluations in the multiplicative subgroup H of F, with order n = 2^i. 
"""

from sage.all import GF as __GF, PolynomialRing as __PolynomialRing

F = __GF(21888242871839275222246405745257275088548364400416034343698204186575808495617)  # finite field F (order of the elliptic curve bn128)
PR = __PolynomialRing(F, "X")  # polynomial ring over F with variable X


def __get_multiplicative_subgroup(n=2**16) -> "tuple[int, int, tuple[int], int, int]":
    # order of the multiplicative subgroup H of the field F
    global F
    p = F.cardinality()
    n = n if n == 1 << (n.bit_length() - 1) else 2**16  # n must be a power of 2, default to 2^16
    assert (p - 1) % n == 0
    omega = F.multiplicative_generator()**((p - 1) // n)  # generator of H (the multiplicative generator of F is always 5 in bn128 order p)
    H = tuple(omega**i for i in range(n))  # multiplicative subgroup H of the field F

    _legendre_symbol = lambda a: pow(a, (p - 1) // 2, p)

    import random
    random.seed(0)  # for reproducibility
    random_element = lambda: F(random.randrange(p))

    if _legendre_symbol(omega) == -1:
        raise ValueError("Invalid generator of H")

    k1 = random_element()
    while _legendre_symbol(k1) != -1 or k1 in H:
        k1 = random_element()

    _k1_inv = pow(k1, -1, p)
    
    k2 = random_element()
    while _legendre_symbol(k2) != -1 or k2 in H or k2 * _k1_inv in H:
        k2 = random_element()
    
    return n, omega, H, k1, k2


__subgroup_size_to_subgroup_data = {
    64: (9088801421649573101014283686030284801466796108869023335878462724291607593530, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    128: (10359452186428527605436343203440067497552205259388878191021578220384701716497, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    256: (3478517300119284901893091970156912948790432420133812234316178878452092729974, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    512: (6837567842312086091520287814181175430087169027974246751610506942214842701774, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    1024: (3161067157621608152362653341354432744960400845131437947728257924963983317266, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    2048: (1120550406532664055539694724667294622065367841900378087843176726913374367458, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    4096: (4158865282786404163413953114870269622875596290766033564087307867933865333818, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    8192: (197302210312744933010843010704445784068657690384188106020011018676818793232, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    16384: (20619701001583904760601357484951574588621083236087856586626117568842480512645, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    32768: (20402931748843538985151001264530049874871572933694634836567070693966133783803, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193), 
    65536: (421743594562400382753388642386256516545992082196004333756405989743524594615, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193),
    131072: (12650941915662020058015862023665998998969191525479888727406889100124684769509, 4031698439758386108298207702947335599159308203342976436122585714817887257092, 9558556555781521338464785745227970311871900686026615027333530183958238975193),
}

if not __subgroup_size_to_subgroup_data:
    __lower_bound = 6
    __upper_bound = 17
    __subgroup_size_to_subgroup_data = dict()
    for i in range(__lower_bound, __upper_bound + 1):
        print(f"Generating multiplicative subgroup of order {2**i}...")
        n, omega, H, k1, k2 = __get_multiplicative_subgroup(2**i)
        __subgroup_size_to_subgroup_data[n] = (omega, k1, k2)
    print(f"Generated multiplicative subgroups of orders 2^{__lower_bound} to 2^{__upper_bound}.")
    print(__subgroup_size_to_subgroup_data)

possible_subgroup_sizes = list(__subgroup_size_to_subgroup_data.keys())


def get_multiplicative_subgroup(n: int) -> "tuple[int, int, tuple[int], int, int]":
    """ Get the multiplicative subgroup of the field F of order n (= 2^i, with 6 <= i <= 16) """
    global F, possible_subgroup_sizes, __subgroup_size_to_subgroup_data
    if n not in possible_subgroup_sizes:
        raise ValueError(f"No multiplicative subgroup of order {n} found")
    omega, k1, k2 = map(F, __subgroup_size_to_subgroup_data[n])
    H = tuple(omega**i for i in range(1, n + 1))  # multiplicative subgroup H of the field F
    return n, omega, H, k1, k2


def __bit_reverse(x: int, n: int) -> int:
    """ Reverse the bits of x, assuming it is represented with n bits """
    y = 0
    for i in range(n):
        y = (y << 1) | (x & 1)
        x >>= 1
    return y


def __dft(points: "list[int]") -> "list[int]":
    """
    DFT as of Cooley-Tukey algorithm, adapted from https://github.com/scipr-lab/libfqfft.git \\
    (method _basic_serial_radix2_FFT in libfqfft/evaluation_domain/domains/basic_radix2_domain_aux.tcc, line 40-79) 
    """
    global F
    n, omega = get_multiplicative_subgroup(len(points))[:2]
    points = list(map(F, points))

    for i in range(n):
        j = __bit_reverse(i, n.bit_length() - 1)
        if j <= i:
            continue
        points[i], points[j] = points[j], points[i]
    
    m = 1
    for _ in range(n.bit_length() - 1):
        w_m = omega**(n // (2 * m))
        for k in range(0, n, 2 * m):
            w = F(1)
            for j in range(m):
                t = w * points[k + j + m]
                points[k + j + m] = points[k + j] - t
                points[k + j] += t
                w *= w_m
        m *= 2
    return points


def __dft_inv(points: "list[int]") -> "list[int]":
    """ INV-DFT as of Cooley-Tukey algorithm """
    global F
    p = F.cardinality()
    n = get_multiplicative_subgroup(len(points))[0]
    points = __dft(points)
    n_inv = pow(n, -1, p)
    return [n_inv * points[0]] + [n_inv * point for point in reversed(points[1:])]


def poly_from_evals_in_H(evals: "list[int]") -> "list[int]":
    """
    Interpolate a polynomial from its evaluations in H ordered by increasing powers of omega, 
    i.e. omega, omega^2, ..., omega^(n - 1), omega^n = omega^0 = 1
    """
    global PR, __subgroup_size_to_subgroup_data, __lower_bound, __upper_bound
    if len(evals) not in __subgroup_size_to_subgroup_data:
        raise ValueError(f"Expected evaluations in H of order 2^{__lower_bound} to 2^{__upper_bound}, not {len(evals)}")
    return PR(__dft_inv(evals[-1:] + evals[:-1]))


# Expose the following functions and variables
__all__ = ["F", "get_multiplicative_subgroup", "poly_from_evals_in_H"]


if __name__ == "__main__":
    import time, random
    n, omega, H, k1, k2 = get_multiplicative_subgroup(2**17)
    print(f"Interpolating a random polynomial of degree {n - 1}...")
    points = [F.random_element() for _ in range(n)]
    start = time.time()
    f = poly_from_evals_in_H(points)  # random polynomial of degree n - 1
    print(f"Elapsed time: {time.time() - start} s")
    i = random.randrange(n)
    assert f(H[i]) == points[i]
