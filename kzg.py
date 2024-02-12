"""
Module for the KZG polynomial commitment scheme (https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf).

This module does not implement the open algorithm, as it is not needed for the Plonk proof system.
"""

from typing import Any, Iterable
from ecc import G1, G2, e


def _gen_slice(params: "tuple[int, int, G1, int, int]") -> "list[G1]":
    x, o, g1, slice_size, start = params
    return [pow(x, i, o) * g1 for i in range(start, start + slice_size)]

def _commit_slice(params: "tuple[list[int], list[G1], int]") -> "G1":
    poly, srs, slice_size = params
    return sum((c * srs[i] for i, c in enumerate(poly[:slice_size])), start=G1.zero())
    

class KZG:
    import multiprocessing

    def __init__(self, srs=None) -> None:
        """ Initializes the KZG scheme with a structured reference string (SRS) if provided. """
        # may need a check for srs, but it's really expensive to check since it needs len(srs) pairing operations
        self.srs = srs  # structured reference string
        if srs is not None:
            self.d = len(srs) - 2  # upper bound on the degree of the polynomial

    def gen(self, d: int, workers=multiprocessing.cpu_count() // 2, filename="", verbose=False) -> "list[G1 | G2]":
        """ Generates the structured reference string (SRS) for the KZG scheme and saves it to a file if a filename is provided. """
        
        if self.srs is not None:
            raise ValueError("SRS is already generated")
        if getattr(d, "__int__", None) is None:
            raise TypeError(f"Generation of SRS is not defined for: {type(d)}")
        if not isinstance(d, int):
            d = int(d)
        if d < 1:
            raise ValueError("d must be a positive integer")
        self.d = d
        
        import random
        system_random = random.SystemRandom()
        x, o = system_random.randrange(G1.order()), G1.order()
        g1, g2 = G1.generator(), G2.generator()

        if verbose:
            print("Generating SRS...")
        slice_size = max(d // (2 * workers), 1)
        from concurrent.futures import ProcessPoolExecutor
        with ProcessPoolExecutor(max_workers=workers) as executor:
            import itertools
            self.srs = list(itertools.chain.from_iterable(executor.map(_gen_slice, (
                (x, o, g1, slice_size, i) for i in range(0, d, slice_size)
            )))) + [g2, x * g2]

        del x  # remove the secret key from memory

        if filename and isinstance(filename, str):
            if verbose:
                print(f"Saving SRS to {filename}...")
            
            import os
            if not os.path.exists(os.path.dirname(filename)):
                os.makedirs(os.path.dirname(filename))

            with open(filename, "wb") as f:
                for p in self.srs[1:-2]:
                    f.write(p.to_bytes())
                f.write(self.srs[-1].to_bytes())
        
    def commit(self, poly: Any, workers=multiprocessing.cpu_count() // 2, verbose=False) -> "G1":
        """ Commit to a polynomial of degree < d using the SRS. """
        
        if self.srs is None:
            raise ValueError("SRS is not generated")
        
        if getattr(poly, "list", None) is None and not isinstance(poly, Iterable):
            raise TypeError(f"Commitment is not defined for: {type(poly)}")
        poly = list(poly) or [0]
        
        for c in poly:
            if getattr(c, "__int__", None) is None:
                raise TypeError(f"Commitment is not defined for coefficient: {type(c)}")
        poly = list(map(int, poly))
        
        if len(poly) > self.d:
            raise ValueError(f"Polynomial degree {len(poly) - 1} exceeds SRS upper bound degree {self.d}")

        if verbose:
            print("Committing to polynomial...")
        slice_size = max(len(poly) // (2 * workers), 1)
        from concurrent.futures import ProcessPoolExecutor
        with ProcessPoolExecutor(max_workers=workers) as executor:
            return sum(executor.map(_commit_slice, (
                (poly[i:i + slice_size], self.srs[i:i + slice_size], slice_size)
            for i in range(0, len(poly), slice_size))), start=G1.zero())

    def import_srs(self, filename: str, verbose=False) -> None:
        """ Import the SRS from a file. """
        if self.srs is not None:
            raise ValueError("SRS is already generated")
        if not isinstance(filename, str):
            raise TypeError(f"Import of SRS is not defined for: {type(filename)}")
        
        if verbose:
            print(f"Importing SRS from {filename}...")
        with open(filename, "rb") as f:
            data = f.read()
        
        self.srs = [G1.generator()] + [G1.from_bytes(data[i:i + G1.bytes_size]) for i in range(0, len(data) - G2.bytes_size, G1.bytes_size)]
        self.srs += [G2.generator(), G2.from_bytes(data[-G2.bytes_size:])]
        self.d = len(self.srs) - 2


# Expose the following class
__all__ = ["KZG"]


if __name__ == "__main__":
    from field import PR, F
    import time
    X = PR.gen()
    d = 2**10
    k = 3

    kzg = KZG()
    kzg.gen(d, verbose=True)

    print(f"Perform batched KZG open on a random set of {k} polynomials...")

    # first polynomial set
    f1s = [PR.random_element(d - 1) for _ in range(k)]
    z1 = F.random_element()
    s1s = [f(z1) for f in f1s]

    v1 = F.random_element()
    h1 = PR(sum((f - s) * v1**i for i, f, s in zip(range(k), f1s, s1s)) / (X - z1))
    assert sum((f - s) * v1**i for i, f, s in zip(range(k), f1s, s1s)) == h1 * (X - z1)

    # second polynomial set
    f2s = [PR.random_element(d - 1) for _ in range(k)]
    z2 = F.random_element()
    s2s = [f(z2) for f in f2s]

    v2 = F.random_element()
    h2 = PR(sum((f - s) * v2**i for i, f, s in zip(range(k), f2s, s2s)) / (X - z2))
    assert sum((f - s) * v2**i for i, f, s in zip(range(k), f2s, s2s)) == h2 * (X - z2)

    g1, g2 = G1.generator(), G2.generator()
    assert g1 == kzg.srs[0] and g2 == kzg.srs[-2]
    x_g2 = kzg.srs[-1]

    print(f"Committing to {k * 2} polynomials of degree: {d - 1}")
    start = time.time()
    cm_f1s = [kzg.commit(f, verbose=True) for f in f1s]
    cm_f2s = [kzg.commit(f, verbose=True) for f in f2s]
    print(f"Commitment time: {time.time() - start} s")

    print(f"Committing to 2 quotient polynomials of degree: {d - 1}")
    start = time.time()
    cm_W1 = kzg.commit(h1, verbose=True)
    cm_W2 = kzg.commit(h2, verbose=True)
    print(f"Commitment time: {time.time() - start} s")

    u = F.random_element()
    cm_F = sum((v1**i * cm_f for i, cm_f in enumerate(cm_f1s)), start=G1.zero()) \
         + u * sum((v2**i * cm_f for i, cm_f in enumerate(cm_f2s)), start=G1.zero())
    cm_E = (
        sum(s * v1**i for i, s in enumerate(s1s)) + u * sum(s * v2**i for i, s in enumerate(s2s))
    ) * g1

    print("Verifying commitments...")
    start = time.time()
    assert e(cm_F - cm_E + z1 * cm_W1 + u * z2 * cm_W2, g2) * e(-cm_W1 - u * cm_W2, x_g2) == 1
    print(f"Verification time: {time.time() - start} s")
    
    print("All tests passed!")
