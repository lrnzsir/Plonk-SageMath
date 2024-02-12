# Plonk-SageMath

This repository contains a SageMath implementation of the [Plonk zk-SNARK](https://eprint.iacr.org/2019/953.pdf).

The only dependency is the [SageMath](http://www.sagemath.org/) library. To install it from a package manager see [here](https://doc.sagemath.org/html/en/reference/spkg/_sagemath.html). Otherwise, you can build Sage from the source code by following the instructions [here](https://doc.sagemath.org/html/en/installation/source.html).

## Structure

The repository is structured as follows:

- [ecc.py](./ecc.py): Contains an implementation of the elliptic curve [BN128](https://hackmd.io/@jpw/bn254) (aka BN254).

- [field.py](./field.py): Contains the implementation of the finite field arithmetic related to the order of the BN128 curve.

- [kzg.py](./kzg.py): Contains the implementation of the [KZG10](https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf) polynomial commitment scheme.

- [cs.py](./cs.py): Contains the implementation of the constraint system used by Plonk, with two example circuits implemented:
  - `evaluation_poly_of_degree(d)` - evaluation of a polynomial of degree at most `d` with arbitrary coefficients at an arbitrary point.
  - `sha256_proof_of_work(seed_length, target_length, data_length)` - proof of work for the SHA256 hash function for an arbitrary `seed` and `target` of length `seed_length` and `target_length` respectively, and `data` to be hashed of length exactly `data_length`.

- [plonk.py](./plonk.py): Contains the implementation of the Plonk zk-SNARK presented in the [paper](https://eprint.iacr.org/2019/953.pdf)'s last section.

## Performance

Since the chosen language is Python, the performance of the implementation is not optimal. Nonetheless, the implementation is functional and can be used to understand the Plonk zk-SNARK. The performance of the implementation is as follows on an Intel Core i7-8750H CPU @ 2.20GHz:

- Without multi-processing, the time to perform $n$ scalar multiplications in `G1` is approximately 40 times slower than the time to perform $n$ scalar multiplications in the [libff](https://github.com/scipr-lab/libff) library.

- The time to compute a proof for the `evaluation_poly_of_degree(2**10)` circuit is approximately 25 seconds.

- The time to compute a proof for the `sha256_proof_of_work(6, 3, 32)` circuit is approximately 700 seconds.

- The time to verify a proof is approximately 0.7 seconds.
