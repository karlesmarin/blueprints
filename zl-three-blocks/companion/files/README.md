# 🔺 Why three blocks? — supplementary material

Programs, data and certificates of the paper *Why three blocks? The limited augmented Zarankiewicz number in fixed
width* (Carles Marín). 📘 Companion site (blueprint): https://karlesmarin.github.io/blueprints/zl-three-blocks/

Every number of the paper traces to a file here. Indices in the data start at 1, as in the paper.

## 🗂️ Contents

- 📁 `data/` — the witnesses and tables drawn in the figures (JSON): the 22 × 5 three-block configuration, the
  3 × 3 × 5 box, the λ_n modules, the table of z_L(m, n), F_4(m) for m ≤ 40, the two periodic families of Theorem E,
  and the shadow certificates for n ≤ 6.
- 📜 `certificates/` — the canonical-base certificates (Theorem D, n ≤ 6) and the 29 profile certificates of
  Theorem E (`perfiles_n4/`).
- 🧮 `programs/` — the programs, listed below; `tabla_zl_*.jsonl` are the raw outputs of the exhaustive searches.
- 🎨 `figures/` — the scripts that draw the figures; they check every witness again before drawing it.
- 📄 `outputs/` — complete outputs of the checks.

## 🧮 Programs

| File | What it computes or checks |
|---|---|
| `zl.py` | Admissibility checker of Definition 2.1 (both readings of (C3)); exact small values as controls. |
| `comprobar_literal_def.py` | Second, independent admissibility checker: Definition 2.1 read literally, cell by cell. |
| `zl_cert_sombras.py` | Proposition 6.1: rational dual certificates for every orbit of shadows (n <= 6). |
| `cert_sombras_check.py` | Independent checker of the shadow certificates (standard library + Fraction). |
| `zl_sombras_mip.py` | Theorem B, n = 7: the shadow as 0/1 variables in one mixed integer program (floating point, evidence only). |
| `zl_cert_canonica.py` | Theorem D, n <= 6: rational dual certificates for the canonical base (anchor column fixed). |
| `cert_canonica_check.py` | Independent checker of the canonical certificates. |
| `zl_perfiles.py` | Theorem E and Appendix A: the exact profile system (types, ports, permitted pairs), one LP per profile. |
| `zl_perfiles_dual.sage` | Theorem E: exact rational duals of the profile LPs (Sage, PPL backend). |
| `cert_perfiles_check.py` | Independent checker of the 29 profile certificates: rebuilds types, ports and permitted pairs from scratch. |
| `f4_familias_check.py` | Theorem E, lower bound: the two periodic families (data/F4_families.json) checked by both checkers, profile per residue. |
| `zl_rho_realiza.py` | Theorem C: realization of an optimal shadow program as an actual configuration (also --canonica for Theorem D). |
| `zl_rho_exacto.sage` | Theorems C and D, n <= 5: the slopes by exact linear programming in Sage. |
| `modulos_lambda.py` | Theorem B, lower bound: the three-block modules for n = 3..12, checked by both checkers. |
| `zl_tipos.py` | Section 7: F_n(m) exactly by the integer program over row types (CP-SAT). |
| `tres_bloques_dual_check.py` | Proposition 6.3: weights, row budgets, modules and the maximum lambda_n in exact arithmetic, every partition with n <= 60. |
| `tres_bloques_identidades.py` | Proposition 6.3: the two deficit identities, symbolically (SymPy). |
| `cruce_escalera_m3.py` | Section 5: the three-column ladder 1/2, 2/3, 1 against the published formulas. |
| `zl_nauty.py` | Section 7: maximum bases up to isomorphism (nauty) and the largest family for each (CP-SAT). |
| `zl_e2_sim.py` | Helper of zl_nauty.py: the family search with and without symmetry breaking. |
| `zl_km.py` | Helper of zl_nauty.py: maximum bases and their automorphisms. |
| `zl_cpsat.py` | Section 7: z(m, n) and the largest family by constraint programming. |
| `zl_cpsat_dlex.py` | Section 7: the same with double-lex symmetry breaking (second, independent run). |
| `tensor_busqueda.py` | Section 8: exhaustive search over the maximum box-free bases of 3 x 3 x p, p <= 5, and their largest admissible families. |

## ▶️ Running the checks

Python 3.10+; `ortools` for the integer and linear programs, `sympy` for the identities, `numpy` for the shadow
orbits, `nauty` (geng, vcolg) for the classes of bases, SageMath for the two `.sage` files. From `programs/`:

```
python cert_sombras_check.py ../data/shadow_certificate_n5.json     # Proposition 6.1
python cert_canonica_check.py ../certificates/cert_canonica_6.json  # Theorem D, n = 6
python cert_perfiles_check.py 4 ../certificates/perfiles_n4         # Theorem E, upper bound
python f4_familias_check.py ../data/F4_families.json 200            # Theorem E, lower bound
python tres_bloques_dual_check.py 60                                # Proposition 6.3
python tres_bloques_identidades.py                                  # Proposition 6.3, identities
python tensor_busqueda.py 5                                         # Proposition 8.1 and Section 8
python zl.py                                                        # the checker and its controls
```

## ✅ What is certified and what is computed

- ✅ **Certified** (finite certificate checked in exact arithmetic by an independent program): the slopes for n ≤ 6
  (Proposition 6.1), the canonical slopes for n ≤ 6 (Theorem D), F_4(m) for every m ≥ 6 (Theorem E).
- 💻 **Computed** (exhaustive search, or a witness checked by both checkers): the new exact values of Section 7
  (nauty and CP-SAT reaching proven optimality, not independently checked certificates), Proposition 8.1.
- 📈 **Evidence only**: the value 1.8 for n = 7 (floating point).

The paper's text prevails; a computation is reported for exactly the part it covers. Comments inside the programs are
partly in Spanish.
