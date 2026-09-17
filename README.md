# AIR-DEEP-FRI Battery Passport — Numerical Verifier & Benchmark

Companion code for the article:

> **ZK-STARK over the Goldilocks Field for Verifiable Compliance of the
> European Battery Passport: AIR Arithmetization, NTT/INTT Interpolation,
> and Zero-Knowledge Parity Constraint**

Two Python scripts reproduce all numerical results published in the paper:

| Script | Purpose |
|--------|---------|
| `verify_battery_passport.py` | Verifies every numerical claim in the paper (9 modules, ~90 checks) |
| `benchmark.py` | Measures prover and verifier times (10 runs, mean ± std) |

---

## Requirements

Python 3.8 or higher. **No external dependencies** — standard library only
(`hashlib`, `struct`, `math`, `statistics`, `time`).

```bash
python3 --version   # must be >= 3.8
```

---

## Quick start

```bash
# Clone the repository
git clone https://github.com/<your-account>/battery-passport-zk
cd battery-passport-zk

# Run the verifier with the article trace
python3 verify_battery_passport.py 1 1 1 0 1 0 0 1

# Run the performance benchmark (≈ 5 min)
python3 benchmark.py
```

---

## `verify_battery_passport.py` — Numerical Verifier

### Usage

```bash
# Article trace (argument mode)
python3 verify_battery_passport.py 1 1 1 0 1 0 0 1

# Interactive mode (bit-by-bit input)
python3 verify_battery_passport.py
```

### Trace structure  J = (J_0, ..., J_7)

| Index | Criterion | Status |
|-------|-----------|--------|
| J_0 | Raw material origin certification | **Mandatory** |
| J_1 | Legal entity identity (LEI) | **Mandatory** |
| J_2 | Carbon footprint below class threshold (PCF) | Optional |
| J_3 | Responsible sourcing audit (RMC) | Optional |
| J_4 | Minimum recycled content | Optional |
| J_5 | Performance / State of Health (SoH) | Optional |
| J_6 | Audited working conditions | Optional |
| J_7 | End-of-life declaration | **Mandatory** |

**Compliance rule:**
- Part A: J_0 = J_1 = J_7 = 1
- Part B: prod(1 - 2*J_i, i=2..6) = 1  AND  sum(J_i, i=2..6) >= 2

### Modules verified

| Module | Content |
|--------|---------|
| 1 | Goldilocks field: p = 2^64 - 2^32 + 1, ord_p(2) = 192, generators g and h |
| 2 | Domains G (order 8) and L (order 64), nesting G ⊂ L, lemma g^(-4i) = (-1)^i |
| 3 | NTT/INTT interpolation of f and f_P, exact coefficients |
| 4 | Auxiliary trace P, AIR constraints C1–C4 |
| 5 | Quotient polynomials Q_k, exact divisibility, degrees |
| 6 | Soundness bounds: eps_DEEP, kappa* ≈ 60.83, lambda* = 22 |
| 7 | Fiat-Shamir protocol: Merkle roots, challenges alpha_k, OOD point z |
| 8 | DEEP polynomial DEEP(x) = (Q(x) - Q(z)) / (x - z), degree check |
| 9 | FRI query: beta_1, iota_1, Merkle path, folding step |

### Expected output

```
✓ All numerical computations verified.
✓ No errors detected.
```

### Full transcript (article trace J = [1,1,1,0,1,0,0,1])

| Value | Hex |
|-------|-----|
| root(f) | 0xef058014d63fc536... |
| root(f_P) | 0xf1070bf54b4f667e... |
| alpha_1 | 0x515c33d762f528be |
| z | 0x538e11f9819fdb58 |
| Q(z) | 0x66f65295e7974b4e |
| root(DEEP) | 0x9e7ddfc58c9eb81f... |
| beta_1 | 0x6dbf514881a1ed6a |
| iota_1 | 56 |
| DEEP(h^56) | 0xc79c5e565af678b2 |

---

## `benchmark.py` — Performance Benchmark

### Usage

```bash
python3 benchmark.py
```

Runs 10 independent trials per configuration and outputs:
- Console table (mean ± std in milliseconds)
- LaTeX rows ready to paste into `resultats_numeriques.tex`
- TikZ coordinates for the throughput figure
- Key values summary for the article instance (N=8)

### Configurations

**Axis 1** — varying N, blowup = 8 fixed:

| N | \|L\| | Trace |
|---|-------|-------|
| 6 | 48 | synthetic (compliant) |
| **8** | **64** | **exact article trace** |
| 12 | 96 | synthetic (compliant) |
| 24 | 192 | synthetic (compliant) |

**Axis 2** — varying blowup, N = 8 fixed:

| Blowup | \|L\| |
|--------|-------|
| 4 | 32 |
| **8** | **64** |
| 12 | 96 |
| 24 | 192 |

> **Constraint:** N × blowup must divide 192 = ord_p(2), and N ≥ 5
> (at least 2 optional criteria for compliance). Valid values for blowup=8:
> N ∈ {6, 8, 12, 24}.

### Prover throughput formula

```
throughput (op/s) = 1000 / t_gen (ms)
std_throughput    = throughput × (std_gen / mean_gen)
```

### Experimental environment (article results)

| Parameter | Value |
|-----------|-------|
| OS | macOS Monterey 12.7.6 (21H1320) |
| CPU | Intel Core i7 dual-core 2.2 GHz |
| RAM | 8 GB DDR3 1600 MHz |
| Language | Python 3 (exact arithmetic over F_p) |
| Runs | 10 independent runs per configuration |
| Protocol | Full AIR-DEEP-FRI, lambda* = 22 FRI queries |

---

## Encoding convention

All hexadecimal values in the paper are produced with the following
convention, documented in both scripts:

| Element | Encoding |
|---------|----------|
| Field elements F_p | Little-endian 8 bytes (LE64) |
| Merkle leaf i | SHA256(LE64(value_i)) |
| Merkle internal node | SHA256(left_child \|\| right_child) |
| Fiat-Shamir challenge | SHA256(transcript)[:8] as LE64 mod p |
| FRI query index | SHA256(transcript)[:8] as LE64 mod \|L\| |

---

## Goldilocks field

```
p = 2^64 - 2^32 + 1 = 18 446 744 069 414 584 321
```

Used in production by Plonky2 (Polygon Zero), Miden VM, and RISC Zero.
Same field, same NTT/INTT structure — our paper provides the first complete
numerical instance with full transcript reproducibility.

---

## Repository structure

```
battery-passport-zk/
├── README.md
├── verify_battery_passport.py   # numerical verifier (9 modules, ~90 checks)
├── benchmark.py                 # performance benchmark (10 runs)
└── article/
    ├── main.tex
    ├── resultats_numeriques.tex
    └── ...
```

---

## License

MIT License — see `LICENSE` file.
