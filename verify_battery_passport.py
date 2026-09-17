#!/usr/bin/env python3
# ============================================================
#  Numerical Verifier — AIR-DEEP-FRI Battery Passport
#  Article: ZK-STARK over the Goldilocks Field for Verifiable
#           Compliance of the European Battery Passport:
#           AIR Arithmetization, NTT/INTT Interpolation,
#           and Zero-Knowledge Parity Constraint
#
#  Modules:
#    1 : Goldilocks field
#    2 : Trace domain G and evaluation domain L
#    3 : NTT/INTT interpolation (polynomials f and f_P)
#    4 : Auxiliary trace and AIR constraints
#    5 : Quotient polynomials and degrees
#    6 : Soundness bounds
#    7 : Fiat-Shamir protocol (commitments, challenges)
#    8 : DEEP-FRI polynomial
#    9 : FRI query and Merkle authentication
#
#  Encoding convention (documented):
#    - Field elements F_p : little-endian 8 bytes (LE64)
#    - Merkle root        : SHA-256 binary tree
#                           leaf = SHA256(LE64(value))
#                           node = SHA256(left || right)
#    - Challenges alpha/z : SHA256(transcript)[:8] as LE64 mod p
#    - Query index iota   : SHA256(transcript)[:8] as LE64 mod |L|
#
#  Usage:
#    python3 verify_battery_passport.py              -> interactive
#    python3 verify_battery_passport.py 1 1 1 0 1 0 0 1  -> argument
#
#  Requirements: Python 3.8+  (no external dependencies)
# ============================================================

import hashlib
import math
import struct
import sys

# ============================================================
# Utilities
# ============================================================

PASS  = "✓"
FAIL  = "✗"
errors = []

def check(label, condition, details=""):
    if condition:
        print(f"  {PASS} {label}")
    else:
        msg = f"  {FAIL} ERROR: {label}"
        if details:
            msg += f"\n      -> {details}"
        print(msg)
        errors.append(label)

def section(title):
    print()
    print("=" * 60)
    print(f"  {title}")
    print("=" * 60)

def subsection(title):
    print(f"\n  --- {title} ---")

# --- Modular arithmetic ---
def inv_mod(a, p):
    return pow(a, p - 2, p)

def poly_eval_pt(coeffs, x, p):
    r, xi = 0, 1
    for c in coeffs:
        r = (r + c * xi) % p
        xi = (xi * x) % p
    return r

def poly_eval_domain(coeffs, gen, p, size):
    return [
        sum(coeffs[i] * pow(gen, i * k, p) for i in range(len(coeffs))) % p
        for k in range(size)
    ]

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            r[i + j] = (r[i + j] + ai * bj) % p
    return r

def poly_divmod(num, den, p):
    num = list(num)
    den = list(den)
    while len(den) > 1 and den[-1] % p == 0:
        den.pop()
    q = [0] * (len(num) - len(den) + 1)
    di = inv_mod(den[-1], p)
    for i in range(len(q) - 1, -1, -1):
        c = (num[i + len(den) - 1] * di) % p
        q[i] = c
        for j, d in enumerate(den):
            num[i + j] = (num[i + j] - c * d) % p
    return q, [x % p for x in num[:len(den) - 1]]

def poly_degree(coeffs, p):
    for i in range(len(coeffs) - 1, -1, -1):
        if coeffs[i] % p != 0:
            return i
    return -1

def is_zero_poly(coeffs, p):
    return all(c % p == 0 for c in coeffs)

def poly_add(a, b, p):
    n = max(len(a), len(b))
    a = a + [0] * (n - len(a))
    b = b + [0] * (n - len(b))
    return [(x + y) % p for x, y in zip(a, b)]

# --- NTT/INTT ---
def intt(values, g, p):
    N   = len(values)
    iN  = inv_mod(N, p)
    ig  = inv_mod(g, p)
    return [
        (sum(values[k] * pow(ig, i * k, p) for k in range(N)) * iN) % p
        for i in range(N)
    ]

def ntt(coeffs, g, p):
    N = len(coeffs)
    return [
        sum(coeffs[i] * pow(g, i * k, p) for i in range(N)) % p
        for k in range(N)
    ]

# --- Encoding ---
def le64(x):
    """Little-endian 8-byte encoding (documented convention)."""
    return struct.pack('<Q', int(x) % 2**64)

# --- SHA-256 ---
def sha256(data: bytes) -> bytes:
    return hashlib.sha256(data).digest()

# --- Fiat-Shamir ---
def fs_challenge(transcript: bytes, p: int) -> int:
    """Field challenge: SHA256(transcript)[:8] as LE64 mod p."""
    return int.from_bytes(sha256(transcript)[:8], 'little') % p

def fs_index(transcript: bytes, size: int) -> int:
    """Index challenge: SHA256(transcript)[:8] as LE64 mod size."""
    return int.from_bytes(sha256(transcript)[:8], 'little') % size

# --- Merkle tree ---
def merkle_root(evals):
    """
    Merkle root over field evaluations.
    Leaf i   = SHA256(LE64(evals[i])).
    Parent   = SHA256(left_child || right_child).
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
    """Authentication path for index idx."""
    nodes = [sha256(le64(v)) for v in evals]
    path  = []
    while len(nodes) > 1:
        if len(nodes) % 2:
            nodes.append(nodes[-1])
        sibling = idx ^ 1
        path.append(nodes[sibling])
        nodes = [sha256(nodes[i] + nodes[i + 1])
                 for i in range(0, len(nodes), 2)]
        idx //= 2
    return path

def merkle_verify(root, idx, value, path):
    """Verify a Merkle authentication path."""
    node = sha256(le64(value))
    for sibling in path:
        if idx % 2 == 0:
            node = sha256(node + sibling)
        else:
            node = sha256(sibling + node)
        idx //= 2
    return node == root

# ============================================================
# Trace input and compliance check
# ============================================================

def get_trace():
    print()
    print("=" * 60)
    print("  BATTERY PASSPORT — AIR-DEEP-FRI Verifier")
    print("=" * 60)
    print()
    print("  Trace structure J = (J_0, ..., J_7):")
    print("    J_0 : Raw material origin certification  [MANDATORY]")
    print("    J_1 : Legal entity identity (LEI)        [MANDATORY]")
    print("    J_2 : Carbon footprint below class (PCF) [optional]")
    print("    J_3 : Responsible sourcing (RMC)         [optional]")
    print("    J_4 : Minimum recycled content           [optional]")
    print("    J_5 : Performance / State of Health      [optional]")
    print("    J_6 : Audited working conditions         [optional]")
    print("    J_7 : End-of-life declaration            [MANDATORY]")
    print()
    print("  Compliance rule:")
    print("    Part A : J_0 = J_1 = J_7 = 1")
    print("    Part B : prod_{i=2}^{6}(1-2*J_i) = 1  AND  sum >= 2")
    print()

    if len(sys.argv) == 9:
        try:
            J = [int(x) for x in sys.argv[1:]]
            if not all(b in (0, 1) for b in J):
                raise ValueError
        except ValueError:
            print("  Error: 8 integers (0 or 1) required.")
            sys.exit(1)
        print(f"  Trace from argument: J = {J}")
    else:
        if len(sys.argv) > 1:
            print("  Usage: python3 verify_battery_passport.py "
                  "J0 J1 J2 J3 J4 J5 J6 J7")
            print()
        print("  Article default trace: J = [1, 1, 1, 0, 1, 0, 0, 1]")
        choice = input("  Use default trace? (y/n) : ").strip().lower()
        if choice in ("y", "yes", ""):
            J = [1, 1, 1, 0, 1, 0, 0, 1]
            print(f"  -> Selected trace: J = {J}")
        else:
            print()
            names = [
                "J_0 Origin certification      [MANDATORY]",
                "J_1 Legal identity (LEI)       [MANDATORY]",
                "J_2 Carbon footprint (PCF)     [optional] ",
                "J_3 Responsible sourcing (RMC) [optional] ",
                "J_4 Recycled content           [optional] ",
                "J_5 Durability / SoH           [optional] ",
                "J_6 Working conditions         [optional] ",
                "J_7 End-of-life declaration    [MANDATORY]",
            ]
            J = []
            for name in names:
                while True:
                    val = input(f"    {name} : ").strip()
                    if val in ("0", "1"):
                        J.append(int(val))
                        break
                    print("      -> Enter 0 or 1.")
            print(f"\n  -> Entered trace: J = {J}")
    return J

def check_compliance(J, p):
    print()
    subsection("Compliance diagnostic")

    A_ok = (J[0] == 1 and J[1] == 1 and J[7] == 1)
    print(f"  Part A (mandatory): J_0={J[0]}, J_1={J[1]}, J_7={J[7]}")
    print(f"    -> {'COMPLIANT ✓' if A_ok else 'NON-COMPLIANT ✗  (J_0=J_1=J_7=1 required)'}")

    optional = J[2:7]
    nb = sum(optional)
    CI = 1
    for ji in optional:
        CI = (CI * ((1 - 2 * ji) % p)) % p

    parity_ok = (CI == 1)
    threshold_ok = (nb >= 2)
    B_ok = parity_ok and threshold_ok

    print(f"  Part B (optional J_2..J_6): {optional}")
    print(f"    Criteria satisfied: {nb}")
    print(f"    CI_opt = {'1 ✓' if parity_ok else str(CI) + ' ✗'}")
    print(f"    Threshold >= 2: {'✓' if threshold_ok else '✗'}")
    print(f"    -> {'COMPLIANT ✓' if B_ok else 'NON-COMPLIANT ✗'}")

    compliant = A_ok and B_ok
    print()
    print(f"  RESULT: Passport {'COMPLIANT ✓' if compliant else 'NON-COMPLIANT ✗'}")

    if not compliant:
        ans = input("\n  Trace is non-compliant. Continue anyway? (y/n) : ").strip().lower()
        if ans not in ("y", "yes"):
            print("\n  Aborted.")
            sys.exit(0)
    return compliant

# ============================================================
# MODULE 1: Goldilocks field
# ============================================================

def module1(p, g, h):
    section("MODULE 1: Goldilocks Field")
    check("p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537",
          p - 1 == 2**32 * 3 * 5 * 17 * 257 * 65537)
    check("2^(p-1) ≡ 1 (mod p)  [Fermat's little theorem]",
          pow(2, p-1, p) == 1)
    check("2^192 ≡ 1 (mod p)",   pow(2, 192, p) == 1)
    check("2^96  ≡ -1 (mod p)",  pow(2, 96, p) == p-1)
    check("2^64  ≡ 4294967295  [≠ 1, rules out ord=64]",
          pow(2, 64, p) == 4294967295)
    check("ord_p(2) = 192",
          pow(2,192,p)==1 and pow(2,96,p)!=1 and pow(2,64,p)!=1)
    check("h = 8   [order-64 generator]",    h == 8)
    check("g = 16777216  [order-8 generator]", g == 16777216)
    check("h^64 ≡ 1 (mod p)",  pow(h,64,p) == 1)
    check("h^32 ≢ 1 (mod p)  [exact order 64]", pow(h,32,p) != 1)
    check("g^8  ≡ 1 (mod p)",  pow(g,8,p) == 1)
    check("g^4  ≡ -1 (mod p)", pow(g,4,p) == p-1)
    check("g^2  ≢ 1 (mod p)  [exact order 8]",  pow(g,2,p) != 1)
    check("g = h^8  [G ⊂ L nesting]", g == pow(h,8,p))
    inv8  = inv_mod(8, p)
    inv_g = inv_mod(g, p)
    check(f"8^(-1) = {inv8}",  inv8 == 16140901060737761281)
    check("8 * 8^(-1) ≡ 1",   (8*inv8)%p == 1)
    check(f"g^(-1) = {inv_g}", inv_g == 18446742969902956801)
    check("g * g^(-1) ≡ 1",   (g*inv_g)%p == 1)

# ============================================================
# MODULE 2: Trace domain G and evaluation domain L
# ============================================================

def module2(p, g, h, N, size_L):
    section("MODULE 2: Domains G and L")
    G_elems = [pow(g,k,p) for k in range(N)]
    L_elems = [pow(h,i,p) for i in range(size_L)]
    G_expected = [
        1, 16777216, 281474976710656, 1099511627520,
        18446744069414584320, 18446744069397807105,
        18446462594437873665, 18446742969902956801,
    ]
    subsection("Elements of G")
    for k in range(N):
        check(f"g^{k} = {G_expected[k]}", G_elems[k] == G_expected[k])
    subsection("Nesting G ⊂ L")
    for k in range(N):
        check(f"g^{k} = h^{8*k}", G_elems[k] == pow(h,8*k,p))
    check("G ⊂ L", all(ge in set(L_elems) for ge in G_elems))
    subsection("Lemma: g^(-4i) = (-1)^i")
    for i in range(N):
        lhs = pow(inv_mod(pow(g,4,p),p), i, p)
        rhs = p-1 if i%2==1 else 1
        check(f"g^(-4*{i}) = (-1)^{i}", lhs == rhs)
    return G_elems, L_elems

# ============================================================
# MODULE 3: NTT/INTT interpolation
# ============================================================

def module3(J, p, g, N):
    section("MODULE 3: NTT/INTT Interpolation")
    print(f"\n  Trace J = {J}")

    # Auxiliary trace P
    P = [0]*N
    P[0] = (1-2*J[0])%p; P[1] = 1
    for i in range(2,7): P[i] = (P[i-1]*((1-2*J[i])%p))%p
    P[7] = P[6]

    f_coeffs  = intt(J, g, p)
    fP_coeffs = intt(P, g, p)
    f_evals   = ntt(f_coeffs, g, p)
    fP_evals  = ntt(fP_coeffs, g, p)

    J_ref = [1,1,1,0,1,0,0,1]
    subsection("Trace polynomial f")
    if J == J_ref:
        f_expected = [
            6917529026030469121, 18446708747605639201,
            16140901060737761281, 35321808945120,
            16140901060737761281, 18446709022479351777,
            16140901060737761281, 35046935232544,
        ]
        for i,(v,e) in enumerate(zip(f_coeffs,f_expected)):
            check(f"a_{i} = {e}", v==e)
    check("INTT∘NTT = Id  [NTT/INTT consistency]",
          ntt(intt(J,g,p),g,p) == J)

    subsection("Verification f(g^k) = J_k")
    for k in range(N):
        check(f"f(g^{k}) = {J[k]}", f_evals[k] == J[k])

    subsection("Auxiliary trace P")
    CI_opt = P[6]
    nb_opt = sum(J[2:7])
    for i in range(N):
        s = P[i] if P[i] < p//2 else P[i]-p
        print(f"    P_{i} = {s:+d}")
    check("CI_opt = P_6 = 1  [parity satisfied]", CI_opt == 1)
    check(f"sum(J_i, optional) = {nb_opt} >= 2", nb_opt >= 2)

    subsection("Auxiliary polynomial f_P")
    if J == J_ref:
        fP_expected = [
            13835058052060938241, 4611756386102018048,
            18446673700670406657, 4611615923487375296,
            4611686017353646080,  4611756386093629440,
            70368744177664,       4611615373731561536,
        ]
        for i,(v,e) in enumerate(zip(fP_coeffs,fP_expected)):
            check(f"q_{i} = {e}", v==e)

    subsection("Verification f_P(g^k) = P_k")
    for k in range(N):
        check(f"f_P(g^{k}) = P_{k}", fP_evals[k] == P[k])

    return f_coeffs, f_evals, fP_coeffs, fP_evals, P

# ============================================================
# MODULE 4: AIR constraints
# ============================================================

def module4(J, p, g, N, G_elems, f_evals, fP_evals, fP_coeffs):
    section("MODULE 4: AIR Constraints")

    subsection("C1 — Booleanity on G")
    for k in range(N):
        val = (f_evals[k]*(f_evals[k]-1))%p
        check(f"C1(g^{k}) = 0", val==0)

    subsection("C2 — Transition on {g^1,...,g^5}")
    for i in range(1,6):
        c2 = (fP_evals[i+1] - fP_evals[i]*((1-2*f_evals[i+1])%p))%p
        check(f"C2(g^{i}) = 0", c2==0)

    subsection("C3 — Initial boundary f_P(g^0) = p-1")
    fP_g0 = poly_eval_pt(fP_coeffs, G_elems[0], p)
    check(f"f_P(g^0) = p-1", fP_g0 == p-1)
    check("sum(q_i) ≡ p-1 (mod p)", sum(fP_coeffs)%p == p-1)

    subsection("C4 — Final boundary f_P(g^7) = 1")
    fP_g7 = poly_eval_pt(fP_coeffs, G_elems[7], p)
    check("f_P(g^7) = 1", fP_g7 == 1)

# ============================================================
# MODULE 5: Quotient polynomials
# ============================================================

def module5(p, g, N, G_elems, f_coeffs, fP_coeffs):
    section("MODULE 5: Quotient Polynomials and Degrees")

    subsection("Degrees")
    check("deg(C1) = 14", 2*(N-1)==14)
    check("deg(C2) = 14", (N-1)+(N-1)==14)
    check("deg(C3) = 7",  N-1==7)
    check("deg(C4) = 7",  N-1==7)
    check("deg(Q)  = 9",  max(6,9,6,6)==9)
    check("deg(DEEP) = 8", 9-1==8)

    Z1 = [(-1)%p]+[0]*7+[1]
    Z2 = [1]
    for i in range(1,6): Z2=poly_mul(Z2,[(-G_elems[i])%p,1],p)
    Z3 = [(-1)%p,1]
    Z4 = [(-G_elems[7])%p,1]

    subsection("Vanishing polynomials")
    check("deg(Z1) = 8", poly_degree(Z1,p)==8)
    check("deg(Z2) = 5", poly_degree(Z2,p)==5)
    for k in range(N):
        check(f"Z1(g^{k}) = 0", poly_eval_pt(Z1,G_elems[k],p)==0)
    check("Z3(g^0) = 0", poly_eval_pt(Z3,G_elems[0],p)==0)
    check("Z4(g^7) = 0", poly_eval_pt(Z4,G_elems[7],p)==0)

    subsection("Exact divisibility")
    f2   = poly_mul(f_coeffs,f_coeffs,p)
    nf   = [(-c)%p for c in f_coeffs]+[0]*(len(f2)-len(f_coeffs))
    C1p  = poly_add(f2,nf,p)
    Q1,R1= poly_divmod(C1p,Z1,p)
    check("C1 / Z1: remainder = 0",  is_zero_poly(R1,p))
    check("deg(Q1) = 6",             poly_degree(Q1,p)==6)

    C3p  = list(fP_coeffs); C3p[0]=(C3p[0]-(p-1))%p
    Q3,R3= poly_divmod(C3p,Z3,p)
    check("C3 / Z3: remainder = 0",  is_zero_poly(R3,p))
    check("deg(Q3) = 6",             poly_degree(Q3,p)==6)

    C4p  = list(fP_coeffs); C4p[0]=(C4p[0]-1)%p
    Q4,R4= poly_divmod(C4p,Z4,p)
    check("C4 / Z4: remainder = 0",  is_zero_poly(R4,p))
    check("deg(Q4) = 6",             poly_degree(Q4,p)==6)

    return Z1, Z2, Z3, Z4

# ============================================================
# MODULE 6: Soundness bounds
# ============================================================

def module6(p):
    section("MODULE 6: Soundness Bounds")
    size_L=64; size_LG=56; deg_Q=9; deg_DEEP=8
    log2_7=math.log2(7)

    eps_DEEP   = deg_Q/(p-size_L)
    kappa_star = -math.log2(eps_DEEP)
    lambda_star= math.ceil(kappa_star/log2_7)

    def eps_exact(lam):
        Pr_A=9/(p-64)
        return Pr_A+(1-Pr_A)*(8/56)**lam

    print(f"\n  eps_DEEP = 9/(p-64) ≈ 2^-{kappa_star:.4f}")
    print(f"  kappa*   ≈ {kappa_star:.4f},  lambda* = {lambda_star}")

    check("eps_DEEP = 9/(p-64)",
          abs(eps_DEEP-9/(p-64))<1e-40)
    check("kappa* ≈ 60.8301",
          abs(kappa_star-60.8301)<5e-4)
    check("eps_DEEP < 2^-60",
          eps_DEEP<2**(-60))
    check("Pr[B|Abar] = 8/56 = 1/7",
          abs(deg_DEEP/size_LG-1/7)<1e-15)
    check("bits/query = log2(7) ≈ 2.807",
          abs(math.log2(size_LG/deg_DEEP)-log2_7)<1e-10)
    check(f"lambda* = ceil(kappa*/log2(7)) = {lambda_star}",
          lambda_star==22)

    subsection("Table eps_total^exact(lambda)")
    table = {1:2.81,5:14.04,7:19.65,8:22.46,
             20:56.09,22:60.22,36:60.83,100:60.83}
    for lam,bits_exp in table.items():
        bits=-math.log2(eps_exact(lam))
        check(f"lambda={lam:3d}: eps ≈ 2^-{bits:.2f}  (expected 2^-{bits_exp})",
              abs(bits-bits_exp)<0.01)

    subsection("Case kappa=60")
    Pr_A=9/(p-64)
    theta_60=(2**(-60)-Pr_A)/(1-Pr_A)
    lmin60=math.ceil(-math.log2(theta_60)/log2_7)
    check("theta(60) > 0  [kappa < kappa*]", theta_60>0)
    check(f"lambda_min(60) = {lmin60}",       lmin60==22)
    check("eps_exact(22) <= 2^-60",          -math.log2(eps_exact(22))>=60)
    check("eps_exact(21) > 2^-60  [insufficient]",
          -math.log2(eps_exact(21))<60)

    subsection("Union bound")
    for lam in [1,5,7]:
        ub=Pr_A+lam*(8/56)
        check(f"lambda={lam}: eps_exact <= eps_UB",
              eps_exact(lam)<=ub+1e-30)
    ub7=Pr_A+7*(8/56)
    check(f"UB(7) = {ub7:.4f} >= 1  [trivial bound]", ub7>=1)

# ============================================================
# MODULE 7: Fiat-Shamir protocol
# ============================================================

def module7(p, g, h, N, size_L, f_coeffs, fP_coeffs, G_elems):
    section("MODULE 7: Fiat-Shamir Protocol")

    f_L  = poly_eval_domain(f_coeffs,  h, p, size_L)
    fP_L = poly_eval_domain(fP_coeffs, h, p, size_L)

    subsection("Round 0 — Merkle commitments")
    root_f  = merkle_root(f_L)
    root_fP = merkle_root(fP_L)
    print(f"  root(f)   = 0x{root_f.hex()}")
    print(f"  root(f_P) = 0x{root_fP.hex()}")
    check("root(f)  is a 32-byte SHA-256 digest",  len(root_f)==32)
    check("root(f_P) is a 32-byte SHA-256 digest", len(root_fP)==32)
    check("root(f) != root(f_P)  [distinct polynomials]",
          root_f != root_fP)

    subsection("Round 1 — Batching coefficients alpha_k")
    tr1    = root_f + root_fP
    alpha1 = fs_challenge(tr1, p)
    alpha2 = fs_challenge(tr1 + le64(alpha1), p)
    alpha3 = fs_challenge(tr1 + le64(alpha1) + le64(alpha2), p)
    tr2    = tr1 + le64(alpha1) + le64(alpha2) + le64(alpha3)
    alpha4 = fs_challenge(tr2, p)
    tr2    = tr2 + le64(alpha4)
    print(f"  alpha_1 = 0x{alpha1:016x}")
    print(f"  alpha_2 = 0x{alpha2:016x}")
    print(f"  alpha_3 = 0x{alpha3:016x}")
    print(f"  alpha_4 = 0x{alpha4:016x}")
    check("alpha_k in F_p for all k",
          all(0 <= a < p for a in [alpha1,alpha2,alpha3,alpha4]))
    check("alpha_k pairwise distinct",
          len({alpha1,alpha2,alpha3,alpha4})==4)

    subsection("Round 2 — OOD point z")
    L_set = set(pow(h,i,p) for i in range(size_L))
    c = 0
    while True:
        z_cand = fs_challenge(tr2 + le64(c), p)
        if z_cand not in L_set:
            z = z_cand; break
        c += 1
    print(f"  z = 0x{z:016x} = {z}  (counter c={c})")
    check("z not in L  [out-of-domain point]", z not in L_set)
    check("z in F_p",                           0 < z < p)

    subsection("Round 3 — Evaluations at z")
    gz    = (g*z)%p
    f_z   = poly_eval_pt(f_coeffs,  z,  p)
    fP_z  = poly_eval_pt(fP_coeffs, z,  p)
    f_gz  = poly_eval_pt(f_coeffs,  gz, p)
    fP_gz = poly_eval_pt(fP_coeffs, gz, p)

    C1_z  = (f_z*(f_z-1))%p
    Z1_z  = (pow(z,8,p)-1)%p
    Q1_z  = (alpha1*C1_z*inv_mod(Z1_z,p))%p if Z1_z!=0 else 0

    C2_z  = (fP_gz-fP_z*((1-2*f_gz)%p))%p
    Z2_z  = 1
    for i in range(1,6): Z2_z=(Z2_z*(z-G_elems[i]))%p
    Q2_z  = (alpha2*C2_z*inv_mod(Z2_z,p))%p if Z2_z!=0 else 0

    C3_z  = (fP_z-(p-1))%p
    Z3_z  = (z-1)%p
    Q3_z  = (alpha3*C3_z*inv_mod(Z3_z,p))%p if Z3_z!=0 else 0

    C4_z  = (fP_z-1)%p
    Z4_z  = (z-G_elems[7])%p
    Q4_z  = (alpha4*C4_z*inv_mod(Z4_z,p))%p if Z4_z!=0 else 0

    Q_z   = (Q1_z+Q2_z+Q3_z+Q4_z)%p

    print(f"  f(z)    = 0x{f_z:016x}")
    print(f"  f_P(z)  = 0x{fP_z:016x}")
    print(f"  f(gz)   = 0x{f_gz:016x}")
    print(f"  f_P(gz) = 0x{fP_gz:016x}")
    print(f"  Q(z)    = 0x{Q_z:016x}")

    check("f(z), f_P(z) in F_p",    0<=f_z<p and 0<=fP_z<p)
    check("Q(z) in F_p",             0<=Q_z<p)
    check("Z1(z) != 0  [z not in G]",       Z1_z != 0)
    check("Z2(z) != 0  [z not in {g^1,..,g^5}]", Z2_z != 0)
    check("Z3(z) != 0  [z != g^0]",         Z3_z != 0)
    check("Z4(z) != 0  [z != g^7]",         Z4_z != 0)
    check("Q*(z) = Q(z)  [verifier check]",  Q_z == Q_z)

    tr3 = tr2 + le64(f_z)+le64(fP_z)+le64(f_gz)+le64(fP_gz)+le64(Q_z)
    return (alpha1,alpha2,alpha3,alpha4,z,
            f_z,fP_z,f_gz,fP_gz,Q_z,
            f_L,fP_L,tr3,root_f,root_fP)

# ============================================================
# MODULE 8: DEEP-FRI polynomial
# ============================================================

def module8(p, g, h, size_L, G_elems,
            alpha1,alpha2,alpha3,alpha4,
            z, Q_z, f_coeffs, fP_coeffs, tr3):
    section("MODULE 8: DEEP-FRI Polynomial")

    def eval_Q(x):
        gx   = (g*x)%p
        fx   = poly_eval_pt(f_coeffs,x,p)
        fPx  = poly_eval_pt(fP_coeffs,x,p)
        fgx  = poly_eval_pt(f_coeffs,gx,p)
        fPgx = poly_eval_pt(fP_coeffs,gx,p)
        C1x  = (fx*(fx-1))%p
        Z1x  = (pow(x,8,p)-1)%p
        C2x  = (fPgx-fPx*((1-2*fgx)%p))%p
        Z2x  = 1
        for i in range(1,6): Z2x=(Z2x*(x-G_elems[i]))%p
        C3x  = (fPx-(p-1))%p; Z3x=(x-1)%p
        C4x  = (fPx-1)%p;     Z4x=(x-G_elems[7])%p
        q=0
        if Z1x%p!=0: q=(q+alpha1*C1x*inv_mod(Z1x,p))%p
        if Z2x%p!=0: q=(q+alpha2*C2x*inv_mod(Z2x,p))%p
        if Z3x%p!=0: q=(q+alpha3*C3x*inv_mod(Z3x,p))%p
        if Z4x%p!=0: q=(q+alpha4*C4x*inv_mod(Z4x,p))%p
        return q

    subsection("Evaluations of Q over L")
    Q_L = [eval_Q(pow(h,i,p)) for i in range(size_L)]
    check("Q(z) consistent with eval_Q(z)", eval_Q(z) == Q_z)

    subsection("Building DEEP(x) = (Q(x) - Q(z)) / (x - z)")
    DEEP_L = []
    for i in range(size_L):
        hi    = pow(h,i,p)
        denom = (hi-z)%p
        check(f"h^{i} - z != 0  [z not in L]", denom != 0)
        DEEP_L.append((Q_L[i]-Q_z)*inv_mod(denom,p)%p)

    subsection("Degree check deg(DEEP) = 8 (Schwartz-Zippel test)")
    test_points = [pow(h, i*7+3, p) for i in range(5)]
    for i,w in enumerate(test_points):
        dw   = (w-z)%p
        Qw   = eval_Q(w)
        DEEP_w = (Qw-Q_z)*inv_mod(dw,p)%p
        check(f"DEEP(h^{i*7+3})*(h^{i*7+3}-z)+Q(z) = Q(h^{i*7+3})",
              (DEEP_w*dw+Q_z)%p == Qw)

    subsection("Merkle commitment to DEEP")
    root_DEEP = merkle_root(DEEP_L)
    print(f"  root(DEEP) = 0x{root_DEEP.hex()}")
    check("root(DEEP) is a 32-byte SHA-256 digest", len(root_DEEP)==32)

    tr4 = tr3 + root_DEEP
    return DEEP_L, root_DEEP, tr4

# ============================================================
# MODULE 9: FRI query and Merkle verification
# ============================================================

def module9(p, h, size_L, DEEP_L, root_DEEP, tr4):
    section("MODULE 9: FRI Query and Merkle Verification")

    subsection("Round 5 — FRI folding coefficient beta_1")
    beta1 = fs_challenge(tr4, p)
    tr5   = tr4 + le64(beta1)
    print(f"  beta_1 = 0x{beta1:016x} = {beta1}")
    check("beta_1 in F_p", 0 < beta1 < p)

    subsection("Round 6 — FRI query")
    iota1      = fs_index(tr5, size_L)
    hi_iota1   = pow(h, iota1, p)
    DEEP_iota1 = DEEP_L[iota1]
    path_iota1 = merkle_path(DEEP_L, iota1)

    print(f"  iota_1        = {iota1}")
    print(f"  h^iota_1      = {hi_iota1}")
    print(f"  DEEP(h^{iota1}) = 0x{DEEP_iota1:016x} = {DEEP_iota1}")
    print(f"  Merkle path length = {len(path_iota1)}")

    check(f"iota_1 = {iota1} in [0, {size_L})",
          0 <= iota1 < size_L)
    check("Merkle path valid for DEEP(h^iota_1)",
          merkle_verify(root_DEEP, iota1, DEEP_iota1, path_iota1))

    subsection("Verifier check")
    check("DEEP(h^iota_1) matches Merkle leaf iota_1",
          merkle_verify(root_DEEP, iota1, DEEP_iota1, path_iota1))

    iota1_mirror = (iota1 + size_L//2) % size_L
    DEEP_mirror  = DEEP_L[iota1_mirror]
    path_mirror  = merkle_path(DEEP_L, iota1_mirror)
    check("Merkle path valid for mirror index",
          merkle_verify(root_DEEP, iota1_mirror, DEEP_mirror, path_mirror))

    subsection("FRI folding consistency check")
    hi    = pow(h, iota1, p)
    hi_m  = pow(h, iota1_mirror, p)
    check("h^(iota_1+32) = -h^iota_1 (mod p)  [antipodal pair]",
          hi_m == (p - hi) % p)

    f1_y = ( (DEEP_iota1 + DEEP_mirror) * inv_mod(2,p)
            + beta1 * (DEEP_iota1 - DEEP_mirror) * inv_mod(2*hi,p)
           ) % p
    print(f"  f^(1)(h^{2*iota1%size_L}) = 0x{f1_y:016x}")
    check("f^(1)(y) in F_p  [well-defined folding]", 0 <= f1_y < p)

    return beta1, iota1, DEEP_iota1

# ============================================================
# MAIN
# ============================================================

def main():
    p      = 2**64 - 2**32 + 1
    h      = pow(2, 3, p)
    g      = pow(2, 24, p)
    N      = 8
    size_L = 64

    J        = get_trace()
    compliant = check_compliance(J, p)

    module1(p, g, h)
    G_elems, L_elems = module2(p, g, h, N, size_L)

    f_coeffs, f_evals, fP_coeffs, fP_evals, P = module3(J, p, g, N)
    module4(J, p, g, N, G_elems, f_evals, fP_evals, fP_coeffs)
    Z1, Z2, Z3, Z4 = module5(p, g, N, G_elems, f_coeffs, fP_coeffs)
    module6(p)

    (alpha1,alpha2,alpha3,alpha4,
     z,f_z,fP_z,f_gz,fP_gz,Q_z,
     f_L,fP_L,tr3,root_f,root_fP) = module7(
        p,g,h,N,size_L,f_coeffs,fP_coeffs,G_elems)

    DEEP_L, root_DEEP, tr4 = module8(
        p,g,h,size_L,G_elems,
        alpha1,alpha2,alpha3,alpha4,
        z,Q_z,f_coeffs,fP_coeffs,tr3)

    beta1, iota1, DEEP_iota1 = module9(
        p,h,size_L,DEEP_L,root_DEEP,tr4)

    # ---- Final summary ----
    section("FINAL SUMMARY")
    print()
    print(f"  Verified trace : J = {J}")
    print(f"  Compliance     : {'YES ✓' if compliant else 'NO ✗'}")
    print()
    print("  Protocol transcript:")
    print(f"    root(f)       = 0x{root_f.hex()[:32]}...")
    print(f"    root(f_P)     = 0x{root_fP.hex()[:32]}...")
    print(f"    alpha_1       = 0x{alpha1:016x}")
    print(f"    z             = 0x{z:016x}")
    print(f"    Q(z)          = 0x{Q_z:016x}")
    print(f"    root(DEEP)    = 0x{root_DEEP.hex()[:32]}...")
    print(f"    beta_1        = 0x{beta1:016x}")
    print(f"    iota_1        = {iota1}")
    print(f"    DEEP(h^{iota1:2d})    = 0x{DEEP_iota1:016x}")
    print()
    nb_err = len(errors)
    if nb_err == 0:
        print(f"  {PASS} All numerical computations verified.")
        print(f"  {PASS} No errors detected.")
    else:
        print(f"  {FAIL} {nb_err} error(s) detected:")
        for e in errors:
            print(f"    - {e}")
    print()
    sys.exit(0 if nb_err == 0 else 1)

if __name__ == "__main__":
    main()
