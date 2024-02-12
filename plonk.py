""" Plonk proof system implementation in Python using SageMath and py_ecc library. """

from field import (
    F, PR, poly_from_evals_in_H,
    get_multiplicative_subgroup
)
from ecc import G1, G2, e
from kzg import KZG
from cs import ConstraintSystem


class Proof:
    def __init__(self, pi: "tuple[G1 | int, ...]") -> None:
        if len(pi) != 15:
            raise ValueError(f"Expected proof size 15, not {len(pi)}")
        for elem in pi[:9]:
            if not isinstance(elem, G1):
                raise TypeError(f"Invalid element type: {type(elem)}")
            
        self.cm_a, self.cm_b, self.cm_c, self.cm_z, self.cm_t_lower, self.cm_t_middle, self.cm_t_higher, self.cm_W_omega, self.cm_W_omega_zeta = pi[:9]
        self.a_eval, self.b_eval, self.c_eval, self.S1_eval, self.S2_eval, self.z_omega_eval = map(F, pi[9:])

    @staticmethod
    def from_bytes(data: bytes) -> "Proof":
        bytes_to_int = lambda x: F(int.from_bytes(x, "big"))
        bytes_to_G1 = lambda x: G1.from_bytes(x)
        return Proof(
            tuple(bytes_to_G1(data[i:i + G1.bytes_size]) for i in range(0, len(data), G1.bytes_size)) +
            tuple(bytes_to_int(data[i:i + 32]) for i in range(9 * G1.bytes_size, 9 * G1.bytes_size + 6 * 32, 32))
        )
    
    def to_bytes(self) -> bytes:
        int_to_bytes = lambda x: int(x).to_bytes(32, "big")
        G1_to_bytes = lambda g1: g1.to_bytes()
        return b"".join(map(G1_to_bytes, self.pi[:9])) + b"".join(map(int_to_bytes, self.pi[9:]))
    
    @staticmethod
    def import_from(self, filename: str) -> "Proof":
        with open(filename, "rb") as f:
            return self.from_bytes(f.read())

    def export_to(self, filename: str) -> None:
        with open(filename, "wb") as f:
            f.write(self.to_bytes())

    
class Plonk:
    class Oracle:
        def __init__(self, data=b"") -> None:
            import hashlib
            self.__oracle = hashlib.sha256(data)
        
        def update(self, data: bytes) -> None:
            self.__oracle.update(data)
        
        def uniform(self, data=b"") -> int:
            oracle = self.__oracle.copy()
            if data:
                oracle.update(data)
            return F(int.from_bytes(oracle.digest(), "big"))

    def __init__(self):
        self.__setup_done = False
    
    def __import_common_preprocessed_input(self, n: int, filename: str, verbose=False) -> None:
        if verbose:
            print(f"Importing Common Preprocessed Input from {filename}...")

        with open(filename, "rb") as f:
            data = f.read()

        bytes_to_int = lambda x: int.from_bytes(x, "big")
        bytes_to_poly = lambda x: PR([bytes_to_int(x[i:i + 32]) for i in range(0, len(x), 32)])
        
        # order of the multiplicative subgroup H
        n = bytes_to_int(data[:32])
        data = data[32:]

        # permutation map
        sigma_map = [bytes_to_int(data[i:i + 32]) for i in range(0, 3 * n * 32, 32)]
        data = data[3 * n * 32:]

        # gate polynomials
        gate_polys = []
        for _ in range(5):
            gate_polys.append(bytes_to_poly(data[:n * 32]))
            data = data[n * 32:]
        gate_polys = tuple(gate_polys)

        # permutation polynomials
        perm_polys = []
        for _ in range(3):
            perm_polys.append(bytes_to_poly(data[:n * 32]))
            data = data[n * 32:]
        perm_polys = tuple(perm_polys)

        self.common_preprocessed_input = (n, sigma_map, gate_polys, perm_polys)

    def __compute_common_preprocessed_input(self, cs: ConstraintSystem, filename: str, verbose=False) -> None:
        if verbose:
            print("Computing the Common Preprocessed Input...")

        n, omega, H, k1, k2 = self.multiplicative_subgroup

        # gate polynomials
        qL_evals, qR_evals, qO_evals, qM_evals, qC_evals = map(list, zip(*cs._gates))
        
        qL = poly_from_evals_in_H(qL_evals + [0] * (n - len(qL_evals)))
        qR = poly_from_evals_in_H(qR_evals + [0] * (n - len(qR_evals)))
        qO = poly_from_evals_in_H(qO_evals + [0] * (n - len(qO_evals)))
        qM = poly_from_evals_in_H(qM_evals + [0] * (n - len(qM_evals)))
        qC = poly_from_evals_in_H(qC_evals + [0] * (n - len(qC_evals)))

        gate_polys = (qM, qL, qR, qO, qC)

        # permutation polynomials
        index_to_H_coset = lambda i: H[i] if i < n else k1 * H[i - n] if i < 2 * n else k2 * H[i - 2 * cs. n]
        sigma_map = list(map(lambda i: index_to_H_coset(cs._sigma[i]), range(3 * n)))

        S1 = poly_from_evals_in_H(sigma_map[:n])
        S2 = poly_from_evals_in_H(sigma_map[n:2 * n])
        S3 = poly_from_evals_in_H(sigma_map[2 * n:])

        perm_polys = (S1, S2, S3)

        self.common_preprocessed_input = (n, sigma_map, gate_polys, perm_polys)

        if verbose:
            print(f"Saving Common Preprocessed Input to {filename}...")

        int_to_bytes = lambda x: int(x).to_bytes(32, "big")
        poly_to_bytes = lambda poly: b"".join(map(int_to_bytes, list(poly) + [0] * (n - poly.degree() - 1)))

        import os
        if not os.path.exists(os.path.dirname(filename)):
            os.makedirs(os.path.dirname(filename))
        
        with open(filename, "wb") as f:
            f.write(int_to_bytes(n))
            f.write(b"".join(map(int_to_bytes, sigma_map)))
            f.write(b"".join(map(poly_to_bytes, gate_polys)))
            f.write(b"".join(map(poly_to_bytes, perm_polys)))

    def __import_verifier_preprocessed_input(self, filename: str, verbose=False) -> None:
        if verbose:
            print(f"Importing Verifier Preprocessed Input from {filename}...")

        with open(filename, "rb") as f:
            data = f.read()
        
        self.verifier_preprocessed_input = \
            tuple(G1.from_bytes(data[i:i + G1.bytes_size]) for i in range(0, len(data), G1.bytes_size))
    
    def __compute_verifier_preprocessed_input(self, filename: str, verbose=False) -> None:
        if verbose:
            print("Computing the Verifier Preprocessed Input...")

        qM, qL, qR, qO, qC = self.common_preprocessed_input[2]
        S1, S2, S3 = self.common_preprocessed_input[3]

        # gate polynomials commitments
        cm_qM = self.kzg.commit(qM, verbose=verbose)
        cm_qL = self.kzg.commit(qL, verbose=verbose)
        cm_qR = self.kzg.commit(qR, verbose=verbose)
        cm_qO = self.kzg.commit(qO, verbose=verbose)
        cm_qC = self.kzg.commit(qC, verbose=verbose)

        # permutation polynomials commitments
        cm_S1 = self.kzg.commit(S1, verbose=verbose)
        cm_S2 = self.kzg.commit(S2, verbose=verbose)
        cm_S3 = self.kzg.commit(S3, verbose=verbose)

        self.verifier_preprocessed_input = (cm_qM, cm_qL, cm_qR, cm_qO, cm_qC, cm_S1, cm_S2, cm_S3)

        if verbose:
            print(f"Saving Verifier Preprocessed Input to {filename}...")
        
        import os
        if not os.path.exists(os.path.dirname(filename)):
            os.makedirs(os.path.dirname(filename))
        
        with open(filename, "wb") as f:
            f.write(b"".join(map(G1.to_bytes, self.verifier_preprocessed_input)))

    def setup(self, cs: ConstraintSystem, verbose=False) -> None:
        """ Setup the Plonk proof system for a given constraint system.

        Args:
        - cs (ConstraintSystem): The constraint system to setup the proof system for.
        - verbose (bool, optional): Set to True to print the progress of the setup. Defaults to False.

        Raises:
        - RuntimeError: When the setup has already been done.
        - TypeError: When the first argument is not of type ConstraintSystem.
        - ValueError: When the constraint system is not correctly defined.
        - ValueError: When the SRS degree of a SRS found in the file is less than n + 6 (n is the number of gates in the provided constraint system).
        """
        if self.__setup_done:
            raise RuntimeError("The setup of Plonk has already been done")

        if not isinstance(cs, ConstraintSystem):
            raise TypeError(f"First argument expected of type: ConstraintSystem, not {type(cs)}")
        if not cs.is_correctly_defined():
            raise ValueError(f"The constraint system is not correctly defined")
        
        self.multiplicative_subgroup = get_multiplicative_subgroup(cs.n)

        import os
        root = "./setup/"

        # ----------------------------------------
        # SRS Setup
        self.kzg = KZG()

        if not os.path.exists(root + f"kzg/srs-{cs.n.bit_length() - 1}.bin"):
            self.kzg.gen(cs.n + 6, filename=root + f"kzg/srs-{cs.n.bit_length() - 1}.bin", verbose=verbose)
        else:
            self.kzg.import_srs(root + f"kzg/srs-{cs.n.bit_length() - 1}.bin", verbose=verbose)
        
        if self.kzg.d < cs.n + 6:
            raise ValueError(f"Expected SRS degree at least {cs.n + 5}, not {self.kzg.d}")
        
        # ----------------------------------------
        # Common Preprocessed Input

        if os.path.exists(root + f"cpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin"):
            self.__import_common_preprocessed_input(
                cs.n, root + f"cpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin", verbose=verbose
            )
        else:
            self.__compute_common_preprocessed_input(
                cs, root + f"cpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin", verbose=verbose
            )

        # ----------------------------------------
        # Verifier Preprocessed Input
        
        if os.path.exists(root + f"vpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin"):
            self.__import_verifier_preprocessed_input(
                root + f"vpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin", verbose=verbose
            )
        else:
            self.__compute_verifier_preprocessed_input(
                root + f"vpi-{cs.n.bit_length() - 1}/{cs.name.lower()}.bin", verbose=verbose
            )
        
        self.__setup_done = True

    def prover(self, common_input: "tuple[int, list[int]]", w: "list[int]", verbose=False) -> "Proof":
        """ Prove the satisfaction of the constraint system for the given public inputs and witness.

        Args:
        - common_input (tuple[int, list[int]]): Common input for the proof system, where the first element is the number of public inputs and the second element is the list of public inputs (i.e. the statement)
        - w (list[int]): The witness for the statement.
        - verbose (bool, optional): Set to True to print the progress of the proof. Defaults to False.

        Raises:
        - RuntimeError: When the setup has not been done.
        - ValueError: When the public inputs size does not match the public inputs length.
        - ValueError: When the witness length does not match 3 * n (n is the number of gates in the constraint system used for the setup).
        - ValueError: When first ell elements of the witness are not equal to the public inputs.

        Returns:
        - tuple[G1 | int, ...]: The proof for the satisfaction of the constraint system for the given public inputs and witness.
        """
        if not self.__setup_done:
            raise RuntimeError("The setup of Plonk must be done before proving anything")
        
        p = F.cardinality()
        n, omega, H, k1, k2 = self.multiplicative_subgroup
        n, sigma_map, gate_polys, perm_polys = self.common_preprocessed_input
        ell, public_inputs = common_input

        if len(public_inputs) != ell:
            raise ValueError(f"Expected public inputs size {ell}, not {len(public_inputs)}")
        public_inputs = list(map(F, public_inputs))
        
        if len(w) != 3 * n:
            raise ValueError(f"Expected witness size {3 * n}, not {len(w)}")
        w = list(map(F, w))

        if any(x != y for x, y in zip(w, public_inputs)):
            raise ValueError("The witness does not satisfy the public inputs")

        int_to_bytes = lambda x: int(x).to_bytes(32, "big")
        poly_to_bytes = lambda poly: b"".join(map(int_to_bytes, list(poly) + [0] * (n - poly.degree() - 1)))
        
        oracle = Plonk.Oracle()  # define random oracle

        # initialize transcript as concatenatenation of common_preprocessed_input (srs included) and common_input
        oracle.update(int_to_bytes(n) + b"".join(map(G1.to_bytes, self.kzg.srs)))
        oracle.update(b"".join(map(int_to_bytes, sigma_map)))
        oracle.update(b"".join(map(poly_to_bytes, gate_polys)))
        oracle.update(b"".join(map(poly_to_bytes, perm_polys)))
        oracle.update(int_to_bytes(ell) + b"".join(map(int_to_bytes, public_inputs)))

        # polynomials used to compute the proof
        X = PR.gen()
        Z_H = X**n - 1  # polynomial with roots the n-th roots of unity
        L1 = PR(omega * Z_H // (n * (X - omega)))  # first Lagrange polynomial, i.e. L1(omega) = 1, L1(omega^i) = 0 for i = 2, ..., n
        # polynomial with opposite values of the public inputs on the first ell elements of H
        PI = poly_from_evals_in_H([-i for i in public_inputs] + [0] * (n - ell))
        
        qM, qL, qR, qO, qC = gate_polys
        S1, S2, S3 = perm_polys
        
        import random
        system_random = random.SystemRandom()
        blinding_scalars = [F(system_random.randrange(p)) for _ in range(9)]

        # ----------------------------------------
        # Round 1
        if verbose:
            print("Round 1...")

        b1, b2, b3, b4, b5, b6 = blinding_scalars[:6]

        a = (b1 * X + b2) * Z_H + poly_from_evals_in_H(w[:n])
        b = (b3 * X + b4) * Z_H + poly_from_evals_in_H(w[n:2 * n])
        c = (b5 * X + b6) * Z_H + poly_from_evals_in_H(w[2 * n:])

        if verbose:
            print("Computing 3 KZG commitments...")
        cm_a = self.kzg.commit(a, verbose=verbose)
        cm_b = self.kzg.commit(b, verbose=verbose)
        cm_c = self.kzg.commit(c, verbose=verbose)

        # update transcript
        oracle.update(cm_a.to_bytes() + cm_b.to_bytes() + cm_c.to_bytes())
        
        # ----------------------------------------
        # Round 2
        if verbose:
            print("Round 2...")
        
        # permutation challenges
        beta = oracle.uniform(b"\x00")
        gamma = oracle.uniform(b"\x01")

        b7, b8, b9 = blinding_scalars[6:]

        evals = [1]
        num, den = F(1), F(1)
        for i in range(n - 1):
            num *= (w[i] + beta * H[i] + gamma) * \
                   (w[n + i] + k1 * beta * H[i] + gamma) * \
                   (w[2 * n + i] + k2 * beta * H[i] + gamma)
            den *= (w[i] + beta * sigma_map[i] + gamma) * \
                   (w[n + i] + beta * sigma_map[n + i] + gamma) * \
                   (w[2 * n + i] + beta * sigma_map[2 * n + i] + gamma)
            evals.append(num / den)

        # permutation polynomial
        z = (b7 * X**2 + b8 * X + b9) * Z_H + poly_from_evals_in_H(evals)

        if verbose:
            print("Computing 1 KZG commitment...")
        cm_z = self.kzg.commit(z, verbose=verbose)

        # update transcript
        oracle.update(cm_z.to_bytes())
        
        # ----------------------------------------
        # Round 3
        if verbose:
            print("Round 3...")
        
        # quotient challenge
        alpha = oracle.uniform()

        # z evaluated at omega * X i.e. z(omega * X)
        z_omega = PR([c * omega**i for i, c in enumerate(list(z))])  # performed like this to speed up the computation

        # helper polynomials
        _h1 = a * b * qM + a * qL + b * qR + c * qO + qC + PI
        _h2 = (a + beta * X + gamma) * (b + beta * k1 * X + gamma) * (c + beta * k2 * X + gamma) * z \
            - (a + beta * S1 + gamma) * (b + beta * S2 + gamma) * (c + beta * S3 + gamma) * z_omega
        _h3 = (z - 1) * L1

        # quotient polynomial
        t = PR((_h1 + _h2 * alpha + _h3 * alpha**2) // Z_H)
            
        _coeffs = list(t)

        b10, b11 = system_random.randrange(p), system_random.randrange(p)
        t_lower = PR(_coeffs[:n]) + b10 * X**n
        t_middle = PR(_coeffs[n:2 * n]) - b10 + b11 * X**n
        t_higher = PR(_coeffs[2 * n:]) - b11
        # assert t == t_lower + t_middle * X**n + t_higher * X**(2 * n)

        if verbose:
            print("Computing 3 KZG commitments...")
        cm_t_lower = self.kzg.commit(t_lower, verbose=verbose)
        cm_t_middle = self.kzg.commit(t_middle, verbose=verbose)
        cm_t_higher = self.kzg.commit(t_higher, verbose=verbose)

        # update transcript
        oracle.update(cm_t_lower.to_bytes() + cm_t_middle.to_bytes() + cm_t_higher.to_bytes())
        
        # ----------------------------------------
        # Round 4
        if verbose:
            print("Round 4...")

        # evaluation challenge
        zeta = oracle.uniform()

        a_eval = a(zeta)
        b_eval = b(zeta)
        c_eval = c(zeta)
        S1_eval = S1(zeta)
        S2_eval = S2(zeta)
        z_omega_eval = z(omega * zeta)

        # update transcript
        oracle.update(b"".join(map(int_to_bytes, (a_eval, b_eval, c_eval, S1_eval, S2_eval, z_omega_eval))))
        
        # ----------------------------------------
        # Round 5
        if verbose:
            print("Round 5...")
        
        # opening challenge
        v = oracle.uniform()

        # helper polynomials
        _h1 = a_eval * b_eval * qM + a_eval * qL + b_eval * qR + c_eval * qO + qC + PI(zeta)
        _h2 = (a_eval + beta * zeta + gamma) * (b_eval + beta * k1 * zeta + gamma) * (c_eval + beta * k2 * zeta + gamma) * z \
            - (a_eval + beta * S1_eval + gamma) * (b_eval + beta * S2_eval + gamma) * (c_eval + beta * S3 + gamma) * z_omega_eval
        _h3 = (z - 1) * L1(zeta)
        
        # linearisation polynomial
        r = (_h1 + _h2 * alpha + _h3 * alpha**2) - Z_H(zeta) * (t_lower + t_middle * zeta**n + t_higher * zeta**(2 * n))

        # opening proof polynomials
        W_omega = PR((r + (a - a_eval) * v + (b - b_eval) * v**2 + (c - c_eval) * v**3 + (S1 - S1_eval) * v**4 + (S2 - S2_eval) * v**5) // (X - zeta))
        W_omega_zeta = PR((z - z_omega_eval) // (X - zeta * omega))

        if verbose:
            print("Computing 2 KZG commitments...")
        cm_W_omega = self.kzg.commit(W_omega, verbose=verbose)
        cm_W_omega_zeta = self.kzg.commit(W_omega_zeta, verbose=verbose)

        # update transcript
        oracle.update(cm_W_omega.to_bytes() + cm_W_omega_zeta.to_bytes())
        
        # ----------------------------------------
        # After all rounds

        # multipoint evaluation challenge
        u = oracle.uniform()

        # Plonk proof
        pi = Proof((
            cm_a, cm_b, cm_c, cm_z, cm_t_lower, cm_t_middle, cm_t_higher, cm_W_omega, cm_W_omega_zeta,
            a_eval, b_eval, c_eval, S1_eval, S2_eval, z_omega_eval
        ))
        return pi

    def verifier(self, common_input: "tuple[int, list[int]]", pi: "Proof", verbose=False) -> bool:
        """ Verify the satisfaction of the constraint system for the given public inputs and proof.

        Args:
            common_input (tuple[int, list[int]]): Common input for the proof system, where the first element is the number of public inputs and the second element is the list of public inputs (i.e. the statement)
            pi (tuple[G1 | int, ...]): The proof for the satisfaction of the constraint system for the given public inputs and unknown witness (as returned by the prover method)
            verbose (bool, optional): Set to True to print the progress of the verification. Defaults to False.

        Raises:
            RuntimeError: When the setup has not been done.
            ValueError: When the public inputs size does not match the public inputs length.
            ValueError: When the proof size does not match 15.
            TypeError: When an element of the proof is not of type G1 or int.

        Returns:
            bool: True if the proof is valid, False otherwise.
        """
        if not self.__setup_done:
            raise RuntimeError("The setup of Plonk must be done before verifying anything")
        
        n, omega, H, k1, k2 = self.multiplicative_subgroup
        n, sigma_map, gate_polys, perm_polys = self.common_preprocessed_input
        cm_qM, cm_qL, cm_qR, cm_qO, cm_qC, cm_S1, cm_S2, cm_S3 = self.verifier_preprocessed_input
        ell, public_inputs = common_input

        # ----------------------------------------
        # Validate all inputs

        if len(public_inputs) != ell:
            raise ValueError(f"Expected public inputs size {ell}, not {len(public_inputs)}")
        public_inputs = list(map(F, public_inputs))

        if not isinstance(pi, Proof):
            raise TypeError(f"Invalid proof type: {type(pi)}")
        
        cm_a, cm_b, cm_c, cm_z, cm_t_lower, cm_t_middle, cm_t_higher, cm_W_omega, cm_W_omega_zeta = \
            pi.cm_a, pi.cm_b, pi.cm_c, pi.cm_z, pi.cm_t_lower, pi.cm_t_middle, pi.cm_t_higher, pi.cm_W_omega, pi.cm_W_omega_zeta
        
        a_eval, b_eval, c_eval, S1_eval, S2_eval, z_omega_eval = \
            pi.a_eval, pi.b_eval, pi.c_eval, pi.S1_eval, pi.S2_eval, pi.z_omega_eval

        g1, g2, x_g2 = self.kzg.srs[0], self.kzg.srs[-2], self.kzg.srs[-1]

        # ----------------------------------------
        # Validate the proof

        int_to_bytes = lambda x: int(x).to_bytes(32, "big")
        poly_to_bytes = lambda poly: b"".join(map(int_to_bytes, list(poly) + [0] * (n - poly.degree() - 1)))

        oracle = Plonk.Oracle()  # define random oracle

        # initialize transcript as concatenatenation of common_preprocessed_input (srs included) and common_input
        oracle.update(int_to_bytes(n) + b"".join(map(G1.to_bytes, self.kzg.srs)))
        oracle.update(b"".join(map(int_to_bytes, sigma_map)))
        oracle.update(b"".join(map(poly_to_bytes, gate_polys)))
        oracle.update(b"".join(map(poly_to_bytes, perm_polys)))
        oracle.update(int_to_bytes(ell) + b"".join(map(int_to_bytes, public_inputs)))

        # compute challenges
        oracle.update(cm_a.to_bytes() + cm_b.to_bytes() + cm_c.to_bytes())
        beta = oracle.uniform(b"\x00")
        gamma = oracle.uniform(b"\x01")
        oracle.update(cm_z.to_bytes())
        alpha = oracle.uniform()
        oracle.update(cm_t_lower.to_bytes() + cm_t_middle.to_bytes() + cm_t_higher.to_bytes())
        zeta = oracle.uniform()
        oracle.update(b"".join(map(int_to_bytes, (a_eval, b_eval, c_eval, S1_eval, S2_eval, z_omega_eval))))
        v = oracle.uniform()
        oracle.update(cm_W_omega.to_bytes() + cm_W_omega_zeta.to_bytes())
        u = oracle.uniform()

        Z_H_eval = zeta**n - 1  # evaluation at zeta of the polynomial with roots the n-th roots of unity
        Li_eval = lambda i: PR(H[i] * Z_H_eval / (n * (zeta - H[i]))) # evaluation at zeta of the i-th Lagrange polynomial
        L1_eval = Li_eval(0)  # evaluation at zeta of the first Lagrange polynomial, i.e. L1(omega) = 1, L1(omega^i) = 0 for i = 2, ..., n
        # polynomial with opposite values of the public inputs on the first ell elements of H
        PI_eval = sum(-v * Li_eval(i) for i, v in enumerate(public_inputs))

        # r constant term
        r0 = PI_eval - L1_eval * alpha**2 - alpha * (a_eval + beta * S1_eval + gamma) * (b_eval + beta * S2_eval + gamma) * (c_eval + gamma) * z_omega_eval

        # helper commitments
        _cm_h1 = (a_eval * b_eval) * cm_qM + a_eval * cm_qL + b_eval * cm_qR + c_eval * cm_qO + cm_qC
        _cm_h2 = (
            (a_eval + beta * zeta + gamma) * (b_eval + beta * k1 * zeta + gamma) * (c_eval + beta * k2 * zeta + gamma) * alpha + L1_eval * alpha**2 + u
        ) * cm_z
        _cm_h3 = -(a_eval + beta * S1_eval + gamma) * (b_eval + beta * S2_eval + gamma) * alpha * beta * z_omega_eval * cm_S3
        _cm_h4 = -Z_H_eval * (cm_t_lower + cm_t_middle * zeta**n + cm_t_higher * zeta**(2 * n))

        # first part of batched polynomial commitment
        cm_D = _cm_h1 + _cm_h2 + _cm_h3 + _cm_h4

        # full batched polynomial commitment
        cm_F = cm_D + v * cm_a + v**2 * cm_b + v**3 * cm_c + v**4 * cm_S1 + v**5 * cm_S2

        # group-encoded batch evaluation
        cm_E = (-r0 + v * a_eval + v**2 * b_eval + v**3 * c_eval + v**4 * S1_eval + v**5 * S2_eval + u * z_omega_eval) * g1

        # batch validate all evaluations
        return e(zeta * cm_W_omega + (u * zeta * omega) * cm_W_omega_zeta + cm_F - cm_E, g2) * e(-(cm_W_omega + u * cm_W_omega_zeta), x_g2) == 1


__all__ = ["Plonk", "Proof"]


if __name__ == "__main__":
    import os, hashlib, time

    # defaults to False since it's computationally expensive (hours to generate the setup and proof)
    test_sha256_proof_of_work = False  
    
    print("Testing the Plonk class...")

    if not test_sha256_proof_of_work:
        d = 2**10

        print(f"Testing Plonk by proving and verifying that an arbitrary polynomial of degree {d} evaluates correctly at an arbitrary point...")

        # constraint system for the evaluation of a arbitrary polynomial of degree d at an arbitrary point
        cs = ConstraintSystem.evaluation_poly_of_degree(d)
        
        f = PR.random_element(d)  # arbitrary polynomial of degree d
        x = F.random_element()  # arbitrary point
        s = f(x)  # expected result

        # compute the common input
        public_inputs = [x] + list(f)
        ell = len(public_inputs)
        common_input = (ell, public_inputs)

        # compute the witness
        w = cs.compute_witness(public_inputs)
        
        # setup, prove and verify
        plonk = Plonk()
        print("Setting up Plonk...")
        start = time.time()
        plonk.setup(cs, verbose=True)
        print(f"Setup done in {time.time() - start:.2f} seconds")

        print("Proving the satisfaction of the constraint system...")
        start = time.time()
        pi = plonk.prover(common_input, w, verbose=True)
        print(f"Proof computed in {time.time() - start:.2f} seconds")

        print("Verifying the satisfaction of the constraint system...")
        start = time.time()
        assert plonk.verifier(common_input, pi, verbose=True)
        print(f"Proof successfully verified in {time.time() - start:.2f} seconds!")
    else:
        seed_length = 6
        target_length = 3
        data_length = 32

        print(f"Testing Plonk by proving and verifying that an arbitrary data of length {data_length} " \
              f"with an arbitrary known prefix of length {seed_length} satisfies a SHA256 proof of work " \
              f"with an arbitrary target of length {target_length}...")
        
        # constraint system for the SHA256 proof of work
        cs = ConstraintSystem.sha256_proof_of_work(seed_length, target_length, data_length)

        seed = os.urandom(seed_length)  # arbitrary known prefix
        data = seed + os.urandom(data_length - seed_length)  # arbitrary data
        # after some work (proof of work), the data is such that its SHA256 hash has the target as a prefix
        target = hashlib.sha256(data).digest()[:target_length]  # arbitrary target

        # compute the common input
        public_inputs = list(seed) + list(target)
        ell = len(public_inputs)
        common_input = (ell, public_inputs)
        # needed to compute the witness
        witness_data = {"data": data}

        # compute the witness
        w = cs.compute_witness(public_inputs, witness_data)

        # setup, prove and verify
        plonk = Plonk()
        print("Setting up Plonk...")
        start = time.time()
        plonk.setup(cs, verbose=True)
        print(f"Setup done in {time.time() - start:.2f} seconds")  # 780 seconds = 13 minutes

        print("Proving the satisfaction of the constraint system...")
        start = time.time()
        pi = plonk.prover(common_input, w, verbose=True)
        print(f"Proof computed in {time.time() - start:.2f} seconds")  # 700 seconds = 11 minutes and 40 seconds

        print("Verifying the satisfaction of the constraint system...")
        start = time.time()
        assert plonk.verifier(common_input, pi, verbose=True)
        print(f"Proof successfully verified in {time.time() - start:.2f} seconds!")  # 7 seconds

    print("Testing the Plonk class done!")
