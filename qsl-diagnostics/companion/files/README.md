# Companion to "Certified Speed-Limit Diagnostics for Deployed Superconducting Quantum Processors"

Carles Marín (independent researcher). Draft companion, October 2026.

Everything needed to reproduce every number and figure of the paper: the analysis scripts, their outputs, and the
public IBM device snapshots they read. The machine-checked bounds are in the public Lean repository
<https://github.com/karlesmarin/formalizations> (module `Formalizations/Physics/QuantumMechanics/SpeedLimit`).

## Layout

All scripts read their inputs from the folder they live in; run them from this folder.

| Path | Content |
|---|---|
| `*.py` | analysis scripts (one per claim, see the map below) |
| `barrido.csv`, `pares.csv`, `serie.csv`, `mejora_por_cubit_salida.txt` | archived outputs |
| `datos/` | qiskit-ibm-runtime 0.51.0 fake-backend snapshots (`props_*.json`, `conf_*.json`) |
| `datos_pulsos/` | qiskit-terra 0.24.1 snapshots with calibrated pulses (`defs_*.json`, `conf_*.json`) |
| `datos_serie/` | snapshots from 13 Qiskit releases, one folder per (backend, date) |
| `paper/figuras.py`, `paper/figuras_3d.py` | the figures of the paper |
| `ficha_ideas.toml` | the hypotheses H1-H3, written before the sweep |
| `LICENSE`, `NOTICE` | Apache-2.0 for our code; origin and licence of the Qiskit data |
| `cz_best_*.npy` | the saved optimal CZ pulses (witnesses): re-evaluated deterministically by `verificar_cz.py`, `epsilon_cz.py`, `poblacion_cz.py` |
| `cz_tope_*.txt`, `cz_tope_salida.txt`, `anchura_u4d_salida.txt`, `bell_anchura_salida.txt`, `cr_continuacion_salida.txt` | archived logs of the optimal-control runs |
| `pulso_x_r*.npy`, `truncacion_L6_salida.txt`, `rfull_salida.txt` | saved single-qubit X pulses and archived outputs of `truncacion_1q.py` (not re-run when packaging) |
| `*_salida.txt` of the quick scripts | regenerated when the package is built (`cruces_segunda_voz`, `tercera_revision`, `mediana_por_backend`, `toronto_sensibilidad`, `identidad_calibracion`, `cota_cz_refinada`, `verificar_cz`, `epsilon_cz`, `poblacion_cz`) |
| `fuentes/cruce_mg2020.py`, `fuentes/cruce_mg2020_salida.txt` | higher-order cross-resonance check (only our script; the third-party papers are not redistributed) |

## Claim → script → output

| Paper section / claim | Script | Output |
|---|---|---|
| Drive convention c = 1: calibrated π pulse gives 1.148π (c = 2 gives 2.296π), 32 backends | `pulsos_x.py` | printed table |
| omegad · amp identical to 9 digits for equal σ; no closed form for 1.148 | `identidad_omegad.py` | printed |
| Two-level controls of the convention (π/omegad, doubling) | `convencion.py` | printed |
| Single-qubit gap: 41 backends, 1646 qubits, median 11.30 [7.19, 15.54]; falsifier and exclusions | `barrido.py` | `barrido.csv` |
| Two-qubit pairs: 1758 pairs, 43 backends; median ratio 4.22 to π/(2 jq) | `pares.py` | `pares.csv` |
| Cross resonance vs first-order formula: 1212 CX, median θ/(π/2) 1.11; Ω_peak/\|δ\| 0.0907; Ω_CR/Δ 0.451 | `cruce_formulas.py` | printed |
| Per-qubit durations: ×1.09; `cairo` above the cap | `mejora_por_cubit.py` | `mejora_por_cubit_salida.txt` |
| Time series 2021–2025 (13 Qiskit releases) | `serie_temporal.py`, `serie_porque.py` | `serie.csv`, printed |
| Lengthening does not lower the error; stratified controls (retraction of a pooled effect) | `duracion_error.py`, `degradacion.py`, `frecuencia_degradados.py` | printed |
| Certified two-qubit bound: numerical controls (2.6 % from π/(4J); Duhamel; random local control) | `control_dos_cubits.py` | printed |
| m_d for CNOT with extra levels (1/√2 for d = 2, 3) | `cnot_qudit.py`, `cnot_m3.py` | printed |
| Zieliński–Zych inequality scanned for α ∈ (0, 10] | `frontera_zz.py`, `frontera_zz2.py` | printed |
| Optimal control: single qubit law T_min ≈ max(π/Ω, ~1.1·2π/\|δ\|) | `grape_1q.py` | printed |
| Optimal control: cross resonance, qutrit-assisted CZ, Bell with ancillas (scipy versions) | `grape_cr.py`, `grape_cz.py`, `grape_bell.py` | printed |
| Convention from calibrated π pulses (θ/π range over pulse shapes, K(σ)) | `identidad_calibracion.py` | `identidad_calibracion_salida.txt` |
| Backend-weighted median 11.37, clustered-bootstrap interval [11.02, 11.65] | `mediana_por_backend.py` | `mediana_por_backend_salida.txt` |
| Toronto 2021 sensitivity (2.78 with, 2.74 without) | `toronto_sensibilidad.py` | `toronto_sensibilidad_salida.txt` |
| CR with 0.7 drive fraction: monotonicity of the feasible time | `grape_cr_continuacion.py` | `cr_continuacion_salida.txt` |
| Qutrit-assisted CZ, amplitude-cap scan (PyTorch; GPU or CPU, long) | `grape_cz_torch.py` | `cz_tope_salida.txt`, `cz_tope_*.txt`, `cz_best_*.npy` |
| Independent re-evaluation of every saved CZ pulse (infidelity, leakage, phases, \|\|A_k\|\|) | `verificar_cz.py` | `verificar_cz_salida.txt` |
| Robust epsilon for the entangling-time bound: eps(\|++>) and (π/4 − arcsin √eps)/(2J) | `epsilon_cz.py` | `epsilon_cz_salida.txt` |
| Population outside the qubit subspace during the CZ (up to 60 %) | `poblacion_cz.py` | `poblacion_cz_salida.txt` |
| Bell-state preparation with ancillas, width scan | `grape_bell_torch.py`, `grape_anchura.py` | `bell_anchura_salida.txt`, `anchura_u4d_salida.txt` |
| Pulse-area identity omegad·\|amp\|·A_rec = π on 777 qubits (max deviation 1.18e-7); residual 1/(1−e^−2) = 1.15652 | `cruces_segunda_voz.py` | `cruces_segunda_voz_salida.txt` (regenerated) |
| CZ construction in π/(6J) (twirl by W, code in the extreme eigenvectors of Q; code state 5/9 outside the qubit subspace); d-dimensional bounds table | `cruces_segunda_voz.py` | `cruces_segunda_voz_salida.txt` |
| Refined CZ bound T_* ≥ 0.4511/J (lemma Tr[(P_A⊗P_B)H_c²]/4 ≤ 97/32 J², equality case, resulting time bound, T_*(2e-8) ≥ 0.4510/J, the e ≥ 1.9e-6 exclusion at T = 0.45/J); the Lean lemma is `QSL.Exchange.refined_cz_lemma` (the time argument is not formalized) | `cota_cz_refinada.py` | `cota_cz_refinada_salida.txt` (regenerated) |
| Exact Bell preparation by \|12⟩↔\|21⟩ (T = 0.3926/J); Choi-based gate bound 0.392599/J for e = 2e-8; X bound in the trace metric (6 % margin at r ≤ 0.2; IBM cap 2.23–2.37×); r_full = omegad/\|δ\| median 0.351 | `tercera_revision.py` | `tercera_revision_salida.txt` (regenerated) |
| Truncation of the fast X pulse: 4-level pulse at r = 1 degrades with ≥ 5 levels, 6-level pulse converged to 12 levels (long optimization; archived) | `truncacion_1q.py` | `truncacion_L6_salida.txt`, `rfull_salida.txt`, `pulso_x_r*.npy` (saved pulses) |
| Re-evaluation of the saved X pulses with 4, 5, 6, 8, 12 levels and the Duhamel certificate η₄ (4-level pulse at r = 1: 7e-9 in 4 levels, ≈ 7e-4 with more; η₄ = 0.551) | `truncacion_reevaluar.py` | `truncacion_reevaluar_salida.txt` (regenerated) |
| Higher-order (Magesan–Gambetta 2020) cross-resonance check | `fuentes/cruce_mg2020.py` | `fuentes/cruce_mg2020_salida.txt` |

Quick check of the witnesses: `python verificar_cz.py cz_best_d3_M8_T0.5500_a10.0.npy` and
`python epsilon_cz.py cz_best_d3_M8_T0.5500_a10.0.npy` (both run in under a second; need only numpy/scipy).
The `grape_*_torch.py` scripts need PyTorch and are the long runs that produced the `.npy` files.

`serie_temporal.py` downloads the Qiskit releases with `pip download` into `cache_pip/` (not included); the extracted
snapshots it needs are already in `datos_serie/`.

## Environment

Python 3.14 with numpy, scipy, mpmath, sympy, matplotlib, PyMuPDF (figure previews only). The optimal-control scripts
take minutes to hours; their random seeds are fixed in each script.

## Licences

- Scripts and outputs (our code): Apache License 2.0, Copyright 2026 Carles Marín (full text in `LICENSE`), the same
  licence as the Lean repository and the Qiskit data.
- `datos*/`: files from Qiskit (`qiskit-ibm-runtime` 0.51.0, `qiskit-terra` 0.16–0.25), © IBM and contributors,
  Apache License 2.0 (`datos/LICENSE.txt`, `datos_pulsos/LICENSE.txt`); see `NOTICE`. They are IBM's published model
  parameters and calibration snapshots, not measurements made by the author.
