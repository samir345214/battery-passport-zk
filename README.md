# AIR-DEEP-FRI Battery Passport: reference prover and verifier

Reference implementation of the paper

> S. Bouali, *A Transparent STARK over the Goldilocks Field for Battery Passport
> Compliance: Exact AIR, Closed-Form Soundness Bounds and Full Numerical
> Verification*. LyRICA Laboratory, School of Information Sciences (ESI), Rabat.

Every numerical value printed in the paper (polynomial coefficients, Merkle
roots, Fiat-Shamir challenges, out-of-domain point, FRI layers, query
positions, proof size, soundness bounds) is recomputed and checked by the
scripts of this repository. Both scripts use **pure Python 3.8+ and the
standard library only**.

---

## Contents

| File | Role |
|---|---|
| `verify_battery_passport.py` | Prover and verifier for one trace, organised in nine modules; prints every value of the paper |
| `benchmark.py` | Diagnostics on valid and invalid traces (all 256 binary traces, cheating provers, forged and tampered proofs) and performance measurements |
| `legacy/verify_battery_passport_v1.py` | Verifier of version 1.0.0, kept only to reproduce the forged-proof test A6a (see below) |
| `legacy/benchmark_v1.py` | Benchmark of version 1.0.0, for the record |

---

## Quick start

```bash
git clone https://github.com/samir345214/battery-passport-zk.git
cd battery-passport-zk

# Proof and verification for the trace of the paper, J = (1,1,1,0,1,0,0,1)
python3 verify_battery_passport.py

# Any trace of 8 criteria
python3 verify_battery_passport.py 1 1 0 0 0 0 0 1

# Export every value to JSON
python3 verify_battery_passport.py --json values.json

# Diagnostics, then performance (10 runs per configuration)
python3 benchmark.py
python3 benchmark.py --diag          # diagnostics only
python3 benchmark.py --perf          # performance only
python3 benchmark.py --runs 20       # number of timed runs
python3 benchmark.py --list          # verdict of each of the 256 traces
```

Exit codes of `verify_battery_passport.py`: `0` trace accepted, `2` trace
rejected, `1` internal error. `benchmark.py` returns `0` if every diagnostic
agrees with the compliance rule.

---

## The statement being proved

A battery passport is summarised by a binary trace
`J = (J0, ..., J7)`, one bit per lifecycle criterion, placed on the subgroup
`G = <g>` of order 8 of the Goldilocks field `p = 2^64 - 2^32 + 1`
(`g = 2^24`).

| Index | Criterion | Status |
|---|---|---|
| 0 | Raw material origin certification | mandatory |
| 1 | Legal entity identity (LEI) | mandatory |
| 2 | Carbon footprint (PCF) | optional |
| 3 | Responsible sourcing (RMC) | optional |
| 4 | Recycled content | optional |
| 5 | Performance / durability (SoH) | optional |
| 6 | Audited labour conditions | optional |
| 7 | End-of-life declaration | mandatory |

**Compliance rule.** The trace is compliant if and only if
(i) `J0 = J1 = J7 = 1`, and (ii) the number of satisfied optional criteria
`J2 + ... + J6` is even (zero included). The parity rule is a formal proxy
chosen because it admits the smallest exact AIR; see the paper for the
discussion and the cost of a threshold rule (test A7).

**AIR.** Two trace polynomials, `f` (the trace) and `f_P` (a parity
accumulator `P1 = 1`, `Pi = P(i-1) (1 - 2 Ji)`), and four constraints:

| Constraint | Polynomial | Domain |
|---|---|---|
| C1 booleanity | `f(x)^2 - f(x)` | `G` |
| C2 transition | `f_P(gx) - f_P(x) (1 - 2 f(gx))` | `{g^0 .. g^5}` |
| C3 parity | `f_P(x) - 1` | `{g^1, g^6}` |
| C4 mandatory | `f(x) - 1` | `{g^0, g^1, g^7}` |

The AIR accepts exactly the 16 compliant traces among the 256 binary ones.

---

## Protocol (DEEP-ALI + complete FRI)

Evaluation domain `L = <h>`, `h = 8`, `|L| = 64` (blowup 8, rate 1/8).
Every Merkle tree commits to pairs of values at `x` and `-x`.

| Round | Prover | Verifier challenge |
|---|---|---|
| 1 | commits `T`: leaf `j` = `(f(x_j), f(-x_j), f_P(x_j), f_P(-x_j))` | |
| 2 | commits `C`: leaf `j` = `(Q(x_j), Q(-x_j))`, `Q = sum alpha_k C_k / Z_k` | `alpha_1 .. alpha_4` (before `C`) |
| 3 | sends `f(z), f_P(z), f(gz), f_P(gz), Q(z)` | `z` outside `L`; checks `Q*(z) = Q(z)` |
| 4 | DEEP composition `F` of degree <= 7 (not committed) | `gamma_1 .. gamma_5` |
| 5 | FRI: commits folds `F_1` (32 points), `F_2` (16 points), sends constant `F_3` | `beta_0, beta_1, beta_2` |
| 6 | opens `T, C, F_1, F_2` at each query | 20 positions `j_r = H(tr || r) mod 32` |

For each query the verifier checks the four Merkle paths, **recomputes
`F(x)` and `F(-x)` itself from the opened values of `f, f_P, Q`**, and checks
the three folding steps down to the constant `F_3`.

The protocol is **transparent and sound but not zero-knowledge**: the
openings reveal values of the trace polynomials (for the paper's trace, the
first query falls on `x = g` and reveals `J1 = 1`).

### Encoding conventions

- field element: 8 bytes little-endian (`LE64`);
- Merkle leaf: `SHA256(LE64(v_1) || ... || LE64(v_k))`, node: `SHA256(left || right)`;
- Fiat-Shamir: `H(t) = SHA256(t)[0:8]` read as `LE64`, reduced mod `p`
  (challenges) or mod 32 (query positions); every challenge is appended to
  the transcript once drawn; `z` is redrawn with a counter `c` until `z` is
  outside `L`.

---

## Expected output for the paper's trace

`python3 verify_battery_passport.py` ends with

```
VERDICT : ACCEPTED  -- the trace is compliant; the proof verifies
Internal consistency checks of this verifier: 41/41 passed
```

and prints, among others:

| Quantity | Value |
|---|---|
| `root(T)` | `0x37c6cac0ec28b7629b5c81725e3ec53d9e53a8689a649e083186b5db9f6dff04` |
| `z` (counter `c = 0`) | `0xe50d0d6013acb709` |
| `Q(z) = Q*(z)` | `0x9f52af330daa844e` |
| final constant `F_3` | `0xcddbb9da6a0cac66` |
| query positions | `8, 20, 23, 9, 29, 27, 12, 20, 24, 10, 9, 13, 28, 10, 28, 13, 10, 16, 15, 1` |
| proof size | 12,656 bytes (= 624 x 20 + 176) |
| verifier cost | 33 Fiat-Shamir + 420 Merkle = 453 SHA-256, 2 field inversions |

A non-compliant trace stops in the AIR module with an explicit reason, e.g.

```
$ python3 verify_battery_passport.py 1 1 0 0 0 0 0 0
VERDICT : REJECTED  -- the trace is NOT compliant -- C4: mandatory criterion
          not satisfied: J(g^7) = 0 (end-of-life declaration)
```

---

## Soundness parameters

| Quantity | Value |
|---|---|
| out-of-domain error | `eps_OOD = 16 / (p - 64)`, about `2^-60.00` |
| FRI (conjectured, rate 1/8) | 3 bits per query |
| operating point | `lambda* = 20` queries, `eps_total` about `2^-59.00` |
| ceiling | `kappa* = 60.00` bits, set by drawing the challenges in `F_p` |

These are conjectured-security figures for a fully verified reference
instance, not a production parameter set: drawing the challenges in a cubic
extension of the field would remove the 60-bit ceiling (see the paper).

---

## Diagnostics (`benchmark.py --diag`)

| Test | Content | Expected result |
|---|---|---|
| A1 | all 256 binary traces with the honest prover | 16 proofs accepted; 240 traces stopped at the AIR level (16 C3, 112 C4, 112 both) |
| A2 | 300 random traces in `F_p^8` and a targeted non-binary attack | all rejected by C1 |
| A3 | independence of the parity and mandatory layers | confirmed |
| A4 | dishonest prover on the 240 non-compliant traces: (a) remainders dropped, (b) false `Q(z) := Q*(z)` | (a) 240/240 rejected at Round 3, (b) 240/240 rejected by FRI |
| A5 | 13 tamperings of the valid proof | all rejected |
| A6 | forged proofs **without any witness** | (a) accepted 200/200 by the v1.0.0 verifier, (b) rejected 2 x 200/200 by the current verifier |
| A7 | degree cost of a threshold rule "at least k of 5" | `deg Q = 27` for `k = 2` (vs 8 for parity) |

---

## Performance (paper, `benchmark.py --perf`)

macOS Monterey 12.7.6, Intel Core i7 dual-core 2.2 GHz, Python 3.13.2,
10 runs, times in ms.

| Configuration | Proving | Verification | Proof (bytes) |
|---|---|---|---|
| N = 8, blowup 8 (paper) | 1.858 +/- 0.033 | 1.250 +/- 0.082 | 12,656 |
| N = 8, blowup 4 | 1.569 +/- 0.204 | 1.606 +/- 0.055 | 15,056 |
| N = 8, blowup 16 | 3.403 +/- 0.466 | 1.281 +/- 0.190 | 11,456 |
| N = 8, blowup 32 | 6.024 +/- 0.464 | 0.981 +/- 0.025 | 10,736 |
| N = 16, blowup 8 | 4.701 +/- 0.362 | 1.623 +/- 0.040 | 17,488 |
| N = 32, blowup 8 | 12.705 +/- 0.214 | 2.037 +/- 0.048 | 22,960 |

Timings depend on the machine; sizes and all protocol values do not.

---

## Changes from v1.0.0

Version 1.0.0 committed a single DEEP polynomial and checked each query only
against its own Merkle root. The folding coefficient entered the transcript
but no folded layer was committed or checked, and the queried values were
never linked to `f`, `f_P` or `Q`. As a consequence, a proof built **without
any trace** (arbitrary roots, out-of-domain values chosen so that
`Q*(z) = Q(z)`, random DEEP values) was accepted. Test A6a reproduces this
with the v1.0.0 verifier kept in `legacy/`.

Version 2.0.0 fixes the protocol:

- `Q` is committed before `z` is drawn;
- the DEEP-ALI composition `F` is recomputed by the verifier from openings
  of `f`, `f_P` and `Q`;
- FRI is complete: three folding rounds, committed layers `F_1` and `F_2`,
  final constant, consistency checked at every query;
- no rejection of query positions in `G` is needed any more.

As a result the paper's values changed: `lambda* = 20` (was 21), ceiling
60.00 bits (was 61.00), proof size 12,656 bytes (was 4,344). The values
published with v1.0.0 must not be used with this version.

---

## Citation

```bibtex
@misc{code2026,
  author       = {Bouali, S.},
  title        = {{AIR-DEEP-FRI} Battery Passport v2.0.0 --- Reference Prover,
                  Verifier and Benchmark},
  howpublished = {\url{https://github.com/samir345214/battery-passport-zk}},
  year         = {2026},
  note         = {DOI: to be assigned by Zenodo for release v2.0.0}
}
```

## License

MIT.
