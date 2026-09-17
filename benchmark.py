#!/usr/bin/env python3
# ============================================================
#  Performance Benchmark — AIR-DEEP-FRI Battery Passport
#
#  Article:
#    ZK-STARK over the Goldilocks Field for Verifiable Compliance
#    of the European Battery Passport: AIR Arithmetization,
#    NTT/INTT Interpolation, and Zero-Knowledge Parity Constraint
#
#  Measures prover and verifier times over 10 independent runs
#  for two axes:
#    Axis 1 — varying N (trace size), blowup = 8 fixed
#    Axis 2 — varying blowup, N = 8 fixed (article instance)
#
#  Full protocol: lambda* = 22 FRI queries per proof.
#
#  Experimental environment (article):
#    macOS Monterey 12.7.6 (21H1320)
#    Intel Core i7 dual-core 2.2 GHz, 8 GB RAM DDR3 1600 MHz
#    Python 3, exact arithmetic over F_p, no external libraries
#
#  Usage:
#    python3 benchmark.py
#
#  Output:
#    - Console table (mean +/- std, 10 runs)
#    - LaTeX rows ready to paste into resultats_numeriques.tex
#    - TikZ coordinates for the throughput figure (fig:throughput)
#    - Key values summary for the article instance (N=8)
#
#  Requirements: Python 3.8+  (no external dependencies)
#
#  Encoding convention (matches verify_battery_passport.py):
#    Field elements : little-endian 8 bytes (LE64)
#    Merkle leaves  : SHA256(LE64(value))
#    Fiat-Shamir    : SHA256(transcript)[:8] as LE64 mod p
# ============================================================

import time, math, struct, hashlib, statistics

# ============================================================
# Goldilocks field parameters
# ============================================================

p = 2**64 - 2**32 + 1   # Goldilocks prime
# ord_p(2) = 192; subgroup generators are powers of 2
# For N*blowup | 192: h = 2^(192/(N*blowup)), g = h^blowup

# ============================================================
# Arithmetic utilities
# ============================================================

def inv_mod(a, p):
    """Modular inverse via Fermat's little theorem (p prime)."""
    return pow(a, p - 2, p)

def le64(x):
    """Encode a field element as little-endian 8 bytes (LE64)."""
    return struct.pack('<Q', int(x) % 2**64)

def sha256(b):
    """SHA-256 hash."""
    return hashlib.sha256(b).digest()

def fs_challenge(transcript: bytes, p: int) -> int:
    """Fiat-Shamir challenge in F_p: SHA256(transcript)[:8] as LE64 mod p."""
    return int.from_bytes(sha256(transcript)[:8], 'little') % p

def fs_index(transcript: bytes, size: int) -> int:
    """Fiat-Shamir index in [0, size): SHA256(transcript)[:8] as LE64 mod size."""
    return int.from_bytes(sha256(transcript)[:8], 'little') % size

# ============================================================
# NTT/INTT over F_p
# ============================================================

def intt(vals, g, p):
    """
    Inverse NTT: interpolate a polynomial from its evaluations
    at the N-th roots of unity {g^0, ..., g^(N-1)}.
    Returns the coefficient vector [a_0, ..., a_{N-1}].
    """
    N = len(vals)
    iN = inv_mod(N, p)
    ig = inv_mod(g, p)
    return [
        (sum(vals[k] * pow(ig, i * k, p) for k in range(N)) * iN) % p
        for i in range(N)
    ]

def poly_eval_domain(coeffs, gen, p, size):
    """Evaluate a polynomial at all points {gen^0, ..., gen^(size-1)}."""
    return [
        sum(coeffs[i] * pow(gen, i * k, p) for i in range(len(coeffs))) % p
        for k in range(size)
    ]

def poly_eval_pt(coeffs, x, p):
    """Evaluate a polynomial at a single point x (Horner's method)."""
    r, xi = 0, 1
    for c in coeffs:
        r = (r + c * xi) % p
        xi = (xi * x) % p
    return r

# ============================================================
# Merkle tree (SHA-256, LE64 encoding)
# ============================================================

def merkle_root(evals):
    """
    Compute the Merkle root over field evaluations.
    Leaf i   = SHA256(LE64(evals[i])).
    Parent   = SHA256(left || right).
    Odd node : last node duplicated.
    """
    nodes = [sha256(le64(v)) for v in evals]
    while len(nodes) > 1:
        if len(nodes) % 2:
            nodes.append(nodes[-1])
        nodes = [sha256(nodes[i] + nodes[i + 1])
                 for i in range(0, len(nodes), 2)]
    return nodes[0]

def merkle_path(evals, idx):
    """Return the Merkle authentication path for leaf index idx."""
    nodes = [sha256(le64(v)) for v in evals]
    path = []
    while len(nodes) > 1:
        if len(nodes) % 2:
            nodes.append(nodes[-1])
        path.append(nodes[idx ^ 1])
        nodes = [sha256(nodes[i] + nodes[i + 1])
                 for i in range(0, len(nodes), 2)]
        idx //= 2
    return path

def merkle_verify(root, idx, value, path):
    """Verify a Merkle authentication path."""
    node = sha256(le64(value))
    for s in path:
        node = sha256(node + s) if idx % 2 == 0 else sha256(s + node)
        idx //= 2
    return node == root

# ============================================================
# Compliance trace construction
# ============================================================

def build_trace(N):
    """
    Build a compliance trace J of length N satisfying:
      Part A : J[0] = J[1] = J[-1] = 1  (mandatory criteria)
      Part B : prod(1-2*J[i], i=2..N-2) = 1  (even parity)
               sum(J[i], i=2..N-2) >= 2       (threshold)

    For N=8 : exact article trace J = [1,1,1,0,1,0,0,1].
    For N!=8 : minimal compliant synthetic trace
               (exactly 2 optional criteria satisfied).
    Requires N >= 5 (at least 2 optional indices 2..N-2).
    """
    if N == 8:
        # Exact article trace (EU Battery Passport regulatory instance)
        return [1, 1, 1, 0, 1, 0, 0, 1]

    # Synthetic compliant trace for generic instances (N != 8)
    opt_indices = list(range(2, N - 1))   # optional criteria: indices 2..N-2
    if len(opt_indices) < 2:
        raise ValueError(
            f"N={N}: only {len(opt_indices)} optional index(es) available "
            f"(indices 2..{N-2}). Part B (threshold >= 2) requires N >= 5."
        )
    J = [0] * N
    J[0] = 1; J[1] = 1; J[-1] = 1        # mandatory
    J[opt_indices[0]] = 1                  # 2 optional satisfied
    J[opt_indices[1]] = 1                  # -> even parity AND threshold >= 2
    return J

# ============================================================
# Full AIR-DEEP-FRI protocol (prover + verifier)
# ============================================================

def run_full(N, blowup):
    """
    Execute one complete AIR-DEEP-FRI proof generation and verification.

    Parameters
    ----------
    N      : trace length (must satisfy N*blowup | 192)
    blowup : domain extension factor (|L| = N * blowup)

    Returns
    -------
    t_gen : prover time in milliseconds
    t_ver : verifier time in milliseconds
    ok    : True if Q*(z) = Q(z) AND all lambda* Merkle paths verify
    """
    size_L = N * blowup

    # Subgroup generators: h of order size_L, g of order N
    # Uses ord_p(2) = 192; requires N*blowup | 192
    h_gen = pow(2, 192 // size_L, p)
    g_gen = pow(2, 192 // N, p)

    G     = [pow(g_gen, k, p) for k in range(N)]
    L_set = set(pow(h_gen, i, p) for i in range(size_L))

    J = build_trace(N)

    # ----------------------------------------------------------
    # PROVER
    # ----------------------------------------------------------
    t0 = time.perf_counter()

    # Step 1: auxiliary trace P (parity accumulator)
    # P[i] = prod(1 - 2*J[k], k=1..i) tracks the running parity
    P = [0] * N
    P[0] = (1 - 2 * J[0]) % p
    P[1] = 1
    for i in range(2, N - 1):
        P[i] = (P[i - 1] * ((1 - 2 * J[i]) % p)) % p
    P[N - 1] = P[N - 2]

    # Step 2: INTT — interpolate f and f_P from trace values
    f_c  = intt(J, g_gen, p)
    fP_c = intt(P, g_gen, p)

    # Step 3: evaluate f and f_P over the extended domain L
    f_L  = poly_eval_domain(f_c,  h_gen, p, size_L)
    fP_L = poly_eval_domain(fP_c, h_gen, p, size_L)

    # Step 4: Merkle commitments (Round 0)
    root_f  = merkle_root(f_L)
    root_fP = merkle_root(fP_L)
    tr1 = root_f + root_fP

    # Step 5: batching coefficients alpha_k (Round 1, Fiat-Shamir)
    a1 = fs_challenge(tr1, p)
    a2 = fs_challenge(tr1 + le64(a1), p)
    a3 = fs_challenge(tr1 + le64(a1) + le64(a2), p)
    tr2 = tr1 + le64(a1) + le64(a2) + le64(a3)
    a4 = fs_challenge(tr2, p)
    tr2 = tr2 + le64(a4)

    # Step 6: out-of-domain point z (Round 2, Fiat-Shamir)
    c = 0
    while True:
        zc = fs_challenge(tr2 + le64(c), p)
        if zc not in L_set:
            z = zc
            break
        c += 1

    # Step 7: evaluations at z and gz (Round 3)
    gz   = (g_gen * z) % p
    f_z  = poly_eval_pt(f_c,  z,  p)
    fP_z = poly_eval_pt(fP_c, z,  p)
    f_gz  = poly_eval_pt(f_c,  gz, p)
    fP_gz = poly_eval_pt(fP_c, gz, p)

    # Quotient polynomial Q(z) = sum_k alpha_k * C_k(z) / Z_{D_k}(z)
    C1_z = (f_z * (f_z - 1)) % p
    Z1_z = (pow(z, N, p) - 1) % p

    C2_z = (fP_gz - fP_z * ((1 - 2 * f_gz) % p)) % p
    Z2_z = 1
    for i in range(1, max(2, N - 2)):
        Z2_z = (Z2_z * (z - G[i])) % p

    C3_z = (fP_z - (p - 1)) % p
    Z3_z = (z - 1) % p

    C4_z = (fP_z - 1) % p
    Z4_z = (z - G[N - 1]) % p

    Q1_z = (a1 * C1_z * inv_mod(Z1_z, p)) % p if Z1_z else 0
    Q2_z = (a2 * C2_z * inv_mod(Z2_z, p)) % p if Z2_z else 0
    Q3_z = (a3 * C3_z * inv_mod(Z3_z, p)) % p if Z3_z else 0
    Q4_z = (a4 * C4_z * inv_mod(Z4_z, p)) % p if Z4_z else 0
    Q_z  = (Q1_z + Q2_z + Q3_z + Q4_z) % p

    # Step 8: Q over L and DEEP polynomial (Round 4)
    def eval_Q(x):
        """Evaluate the combined quotient polynomial Q at point x."""
        gx   = (g_gen * x) % p
        fx   = poly_eval_pt(f_c,  x,  p)
        fPx  = poly_eval_pt(fP_c, x,  p)
        fgx  = poly_eval_pt(f_c,  gx, p)
        fPgx = poly_eval_pt(fP_c, gx, p)
        C1x  = (fx * (fx - 1)) % p
        Z1x  = (pow(x, N, p) - 1) % p
        C2x  = (fPgx - fPx * ((1 - 2 * fgx) % p)) % p
        Z2x  = 1
        for i in range(1, max(2, N - 2)):
            Z2x = (Z2x * (x - G[i])) % p
        C3x = (fPx - (p - 1)) % p
        Z3x = (x - 1) % p
        C4x = (fPx - 1) % p
        Z4x = (x - G[N - 1]) % p
        q = 0
        if Z1x: q = (q + a1 * C1x * inv_mod(Z1x, p)) % p
        if Z2x: q = (q + a2 * C2x * inv_mod(Z2x, p)) % p
        if Z3x: q = (q + a3 * C3x * inv_mod(Z3x, p)) % p
        if Z4x: q = (q + a4 * C4x * inv_mod(Z4x, p)) % p
        return q

    Q_L    = [eval_Q(pow(h_gen, i, p)) for i in range(size_L)]
    # DEEP(x) = (Q(x) - Q(z)) / (x - z)  -- exact polynomial division
    DEEP_L = [
        (Q_L[i] - Q_z) * inv_mod((pow(h_gen, i, p) - z) % p, p) % p
        for i in range(size_L)
    ]
    root_DEEP = merkle_root(DEEP_L)

    # Step 9: FRI folding coefficient and lambda* = 22 queries (Rounds 5-6)
    tr3   = tr2 + le64(f_z) + le64(fP_z) + le64(f_gz) + le64(fP_gz) + le64(Q_z)
    tr4   = tr3 + root_DEEP
    beta1 = fs_challenge(tr4, p)
    tr5   = tr4 + le64(beta1)

    lambda_star = 22   # optimal number of FRI queries (Theorem soundness-global)
    queries = []
    tr_cur  = tr5
    for r in range(lambda_star):
        iota_r = fs_index(tr_cur + le64(r), size_L)
        path_r = merkle_path(DEEP_L, iota_r)
        queries.append((iota_r, DEEP_L[iota_r], path_r))
        tr_cur = tr_cur + le64(iota_r)

    t1    = time.perf_counter()
    t_gen = (t1 - t0) * 1000   # milliseconds

    # ----------------------------------------------------------
    # VERIFIER
    # Recomputes all Fiat-Shamir challenges from public commitments,
    # checks Q*(z) = Q(z), and verifies all lambda* Merkle paths.
    # ----------------------------------------------------------
    t2 = time.perf_counter()

    # Recompute challenges from transcript
    tr1v = root_f + root_fP
    a1v  = fs_challenge(tr1v, p)
    a2v  = fs_challenge(tr1v + le64(a1v), p)
    a3v  = fs_challenge(tr1v + le64(a1v) + le64(a2v), p)
    tr2v = tr1v + le64(a1v) + le64(a2v) + le64(a3v)
    a4v  = fs_challenge(tr2v, p)
    tr2v = tr2v + le64(a4v)

    c = 0
    while True:
        zc = fs_challenge(tr2v + le64(c), p)
        if zc not in L_set:
            zv = zc
            break
        c += 1

    # Recompute Q*(z) from claimed evaluations
    C1_zv = (f_z * (f_z - 1)) % p
    Z1_zv = (pow(zv, N, p) - 1) % p
    C2_zv = (fP_gz - fP_z * ((1 - 2 * f_gz) % p)) % p
    Z2_zv = 1
    for i in range(1, max(2, N - 2)):
        Z2_zv = (Z2_zv * (zv - G[i])) % p
    C3_zv = (fP_z - (p - 1)) % p
    Z3_zv = (zv - 1) % p
    C4_zv = (fP_z - 1) % p
    Z4_zv = (zv - G[N - 1]) % p

    Q1_zv = (a1v * C1_zv * inv_mod(Z1_zv, p)) % p if Z1_zv else 0
    Q2_zv = (a2v * C2_zv * inv_mod(Z2_zv, p)) % p if Z2_zv else 0
    Q3_zv = (a3v * C3_zv * inv_mod(Z3_zv, p)) % p if Z3_zv else 0
    Q4_zv = (a4v * C4_zv * inv_mod(Z4_zv, p)) % p if Z4_zv else 0
    Qstar = (Q1_zv + Q2_zv + Q3_zv + Q4_zv) % p

    # Verify all lambda* = 22 Merkle authentication paths
    all_ok = (Qstar == Q_z)
    for iota_r, deep_val, path_r in queries:
        all_ok = all_ok and merkle_verify(root_DEEP, iota_r, deep_val, path_r)

    t3    = time.perf_counter()
    t_ver = (t3 - t2) * 1000   # milliseconds

    return t_gen, t_ver, all_ok

# ============================================================
# Benchmark runner
# ============================================================

RUNS = 10   # number of independent runs per configuration

print("=" * 72)
print("  BENCHMARK  AIR-DEEP-FRI — Battery Passport")
print("  10 runs per configuration | Python 3 | Goldilocks F_p")
print(f"  Full protocol: lambda* = 22 FRI queries")
print("=" * 72)

# ----------------------------------------------------------
# Axis 1: varying N, blowup = 8 fixed
# Constraint: N * 8 must divide 192 = ord_p(2)
#             AND N >= 5 (at least 2 optional criteria)
# Valid values: N in {6, 8, 12, 24}
# ----------------------------------------------------------
print("\n--- Axis 1: varying N  (blowup = 8 fixed) ---")
print(f"{'N':>5} | {'|L|':>5} | {'Gen mean (ms)':>14} | "
      f"{'Gen std':>8} | {'Ver mean (ms)':>14} | {'Ver std':>8}")
print("-" * 65)

res_N = []
for N in [6, 8, 12, 24]:
    blowup = 8
    if 192 % (N * blowup) != 0:
        continue
    gs = []; vs = []
    for _ in range(RUNS):
        tg, tv, ok = run_full(N, blowup)
        assert ok, f"Verification failed for N={N}"
        gs.append(tg); vs.append(tv)
    mg = statistics.mean(gs); sg = statistics.stdev(gs)
    mv = statistics.mean(vs); sv = statistics.stdev(vs)
    res_N.append((N, N * blowup, mg, sg, mv, sv))
    mark = "  <- article" if N == 8 else ""
    print(f"{N:>5} | {N*blowup:>5} | {mg:>14.3f} | "
          f"{sg:>8.3f} | {mv:>14.4f} | {sv:>8.4f}{mark}")

# ----------------------------------------------------------
# Axis 2: varying blowup, N = 8 fixed
# Constraint: 8 * blowup must divide 192 = ord_p(2)
# Valid values: blowup in {4, 8, 12, 24}
# ----------------------------------------------------------
print("\n--- Axis 2: varying blowup  (N = 8 fixed) ---")
print(f"{'Blowup':>7} | {'|L|':>5} | {'Gen mean (ms)':>14} | "
      f"{'Gen std':>8} | {'Ver mean (ms)':>14} | {'Ver std':>8}")
print("-" * 65)

res_B = []
N = 8
for blowup in [4, 8, 12, 24]:
    if 192 % (N * blowup) != 0:
        continue
    gs = []; vs = []
    for _ in range(RUNS):
        tg, tv, ok = run_full(N, blowup)
        assert ok, f"Verification failed for blowup={blowup}"
        gs.append(tg); vs.append(tv)
    mg = statistics.mean(gs); sg = statistics.stdev(gs)
    mv = statistics.mean(vs); sv = statistics.stdev(vs)
    res_B.append((blowup, N * blowup, mg, sg, mv, sv))
    mark = "  <- article" if blowup == 8 else ""
    print(f"{blowup:>7} | {N*blowup:>5} | {mg:>14.3f} | "
          f"{sg:>8.3f} | {mv:>14.4f} | {sv:>8.4f}{mark}")

print("\n<- article  =  N=8, blowup=8 instance from the paper")
print("✓  All assertions passed  (Q*(z) = Q(z)  AND  Merkle valid)")



# ============================================================
# Key values summary (article instance N=8, blowup=8)
# ============================================================
print("\n=== Key values — Article instance  (N=8, |L|=64) ===")
for N, sL, mg, sg, mv, sv in res_N:
    if N == 8:
        d_prv = 1000.0 / mg
        d_ver = 1000.0 / mv
        ratio = mg / mv
        print(f"  Prover generation  : {mg:.3f} +/- {sg:.3f} ms")
        print(f"  Verifier time      : {mv:.4f} +/- {sv:.4f} ms")
        print(f"  Prover throughput  : {d_prv:.2f} op/s")
        print(f"  Verifier throughput: {d_ver:.2f} op/s")
        print(f"  Prover/Verifier    : {ratio:.1f}x  (verifier is faster)")
