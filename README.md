# 🏛️ Blueprints

🌐 **[Open the library](https://karlesmarin.github.io/blueprints/)**

What each paper proves, how its results depend on each other, and what exactly has been checked. The published companion sites (blueprints) of Carles Marín's papers, with the library page that
indexes them: every statement copied verbatim with the paper's numbering, what it uses and where it is used, and what
was checked besides the written proof.

- 📄 Published versions only: each blueprint follows the version named on its card (DOI), and carries that PDF.
- ✅ What is checked is said statement by statement: 🔗 Lean (linked to karlesmarin/formalizations), 💻 programs,
  🔍 audits.
- 🎬 The paper's figures come alive (3D, sliders), and 🧪 the labs run the paper's own code in the browser.
- 🤖 Generated: do not edit by hand.

## 🧭 How it works

1. 📚 **[The library](https://karlesmarin.github.io/blueprints/)** lists every paper. 🔎 Search all the statements at once (a number, a name, a word);
   🏷️ choose a subject (keyword, MSC code, field, tool); keep only what Lean or a program checked; arrange the papers by
   series, MSC code, the branches they take tools from, what they serve, or the Lean modules.
2. 📘 **A paper's blueprint** is the paper statement by statement, with its numbering. 📄 Paper shows the statements
   and proofs; 🔍 Explore adds explanations, the paper's figures in motion and the labs. On each statement:
   - 📕 the paper (PDF) at its page, in English or, when there is one, in Spanish;
   - 📍 the statement on the map; the dependency icon: what it uses and where it is used;
   - L∃∀N the parts checked in Lean, with links to the code at a fixed commit; 🛡️ what else was checked, and how far;
   - ❝ its citation, ready to copy; ⚠ write to the author about it.
3. 🗺️ **The map** is the whole paper on one page: the main results, the tools they use and what they serve, with the
   graph of all the dependencies (zoom, drag, click a box to read it).
4. 🧪 **The labs** run the paper's own computations in the browser, with values you choose; nothing to install.
5. ⬇ **PDF**: the blueprint and the map can also be downloaded as PDF files, as they look on screen.
6. 🧭 **Tour** and ❓ **How to use**, on every page, show each piece; every button says what it does when the pointer
   rests on it.

## 🚀 Using it

Open [the library](https://karlesmarin.github.io/blueprints/). Or locally:

```
git clone https://github.com/karlesmarin/blueprints.git
cd blueprints
python -m http.server
```

and open `http://localhost:8000/`.

## 🗂️ Contents

| | Paper | Blueprint | Version |
|---|---|---|---|
| 💠 | The irreducible characters of Sp(2m) at every power of Kostant's element: when they vanish, their value as a signed ratio of root products, and their absolute value as a product of dimensions of GL, Sp and odd SO representations. | 📘 [open](https://karlesmarin.github.io/blueprints/characters-at-aP/) · [`characters-at-aP/`](characters-at-aP/) | [10.5281/zenodo.22683560](https://doi.org/10.5281/zenodo.22683560) |
| 🌀 | A sorry-free Lean 4 development of the real dilogarithm (reflection, Landen, duplication, the golden-ratio values without the five-term relation), the Clausen function and Catalan’s constant, the Fejér–Jackson inequality, the Margolus–Levitin and an L¹ Mandelstam–Tamm speed limit, assembled into: the weight-2 zeta state never reaches an orthogonal state. Classical mathematics; the contribution is the formalization and its assembly. | 📘 [open](https://karlesmarin.github.io/blueprints/dilogarithm-clock/) · [`dilogarithm-clock/`](dilogarithm-clock/) | [10.5281/zenodo.20675270](https://doi.org/10.5281/zenodo.20675270) |
| 🌀 | Abel’s five-term relation for the Rogers L-function, L(x)+L(y) = L(xy) + L(x(1−y)/(1−xy)) + L(y(1−x)/(1−xy)) for x, y in (0,1), proved sorry-free in Lean 4 over Mathlib by the classical differentiation argument. Classical mathematics; the contribution is the formalization. | 📘 [open](https://karlesmarin.github.io/blueprints/dilogarithm-pentagon/) · [`dilogarithm-pentagon/`](dilogarithm-pentagon/) | [10.5281/zenodo.20682715](https://doi.org/10.5281/zenodo.20682715) |
| 🎵 | The seven white keys maximize the fifth Fourier magnitude and minimize every strictly convex decreasing pair energy, with the same equality class (the twelve diatonic transpositions); the five black keys inherit both. Classical mathematics, formalized in Lean 4 with exact arithmetic. | 📘 [open](https://karlesmarin.github.io/blueprints/huddling-scales/) · [`huddling-scales/`](huddling-scales/) | [10.5281/zenodo.23121103](https://doi.org/10.5281/zenodo.23121103) |
| 🧩 | For every n ≥ 14, two integer (Conway–Coxeter) frieze patterns of width n − 3 with fewer than four sign changes in a row: strictly ordered middle rows for even n, exactly two sign changes in row ⌊w/2⌋ for odd n (inside the range of Tabachnikov’s Problem 1); 14 and 15 are the smallest n, by exhaustive search. Both families checked in Isabelle/HOL for every n. | 📘 [open](https://karlesmarin.github.io/blueprints/integer-frieze-sign-changes/) · [`integer-frieze-sign-changes/`](integer-frieze-sign-changes/) | [10.5281/zenodo.23656979](https://doi.org/10.5281/zenodo.23656979) |
| 🧩 | Inside the second inversion stage of the free field of the free group of rank three, two chains of subrings are strict at every step and infinitely many stopping steps of the Dubrovin–Gräter–Hanke series occur; the tool is a sufficient criterion for non-membership. | 📘 [open](https://karlesmarin.github.io/blueprints/inversion-height-two/) · [`inversion-height-two/`](inversion-height-two/) | [10.5281/zenodo.23481331](https://doi.org/10.5281/zenodo.23481331) |
| 🕸️ | Jacobi's formula (det M)′ = tr(adj M·M′) for matrices of polynomials and Newton's identity for matrix traces to all orders, through a formal resolvent series, composed with Bass's formula to express the non-backtracking counts tr(Bᵏ) of a graph through its adjacency data; machine-checked in Lean 4. Classical mathematics; the contribution is the formalization. | 📘 [open](https://karlesmarin.github.io/blueprints/jacobi-newton/) · [`jacobi-newton/`](jacobi-newton/) | [10.5281/zenodo.20578469](https://doi.org/10.5281/zenodo.20578469) |
| 📈 | If a real polynomial of degree n has only real roots, its elementary symmetric functions satisfy Newton's inequalities e_k² C(n,k−1) C(n,k+1) ≥ e_{k−1} e_{k+1} C(n,k)² (equivalently, the normalized means are log-concave). Classical mathematics, formalized in Lean 4: the symmetric-function form for monic p, the coefficient form with no normalization. | 📘 [open](https://karlesmarin.github.io/blueprints/newton-inequalities/) · [`newton-inequalities/`](newton-inequalities/) | [10.5281/zenodo.20693063](https://doi.org/10.5281/zenodo.20693063) |
| ⚛️ | The equivalence classes of orbifold boundary conditions form an affine semigroup, identified in the unit-weight sector with cut, group-based and binary hierarchical configurations; thirteen of the cases are complete intersections with explicit gluing trees, the group-based tripod is one exactly when \|G\| ≤ 3, (S¹/Z₂)ᵏ is none for k ≥ 3, and the exceptional product case has a unique minimal Markov basis of 8 + 8 indispensable binomials and Cohen–Macaulay type 9. | 📘 [open](https://karlesmarin.github.io/blueprints/orbifold-semigroup/) · [`orbifold-semigroup/`](orbifold-semigroup/) | [10.5281/zenodo.22254863](https://doi.org/10.5281/zenodo.22254863) |
| 🧮 | At prime height p = n+k, the ring generated by one column of the SU(n)_k S-matrix is the integers of a cyclotomic field tensored with an order that is, locally at p, a monomial ring with value semigroup S_T; the index, the Gorenstein property and the exponent are read off S_T, and S_T off the nonzero power sums of the spectrum when p > (n−1)(n−2) or n ≤ 12. | 📘 [open](https://karlesmarin.github.io/blueprints/s-matrix-orders-I/) · [`s-matrix-orders-I/`](s-matrix-orders-I/) | [10.5281/zenodo.22848529](https://doi.org/10.5281/zenodo.22848529) |
| 🧮 | For the orders generated by the columns of the SU(n)ₖ S-matrix at prime height, the small defects are classified by vanishing power sums, the proportion of columns with defect ≥ 2 is 2/p − 1/p² and the mean defect 1 + 2/p + 3/p² up to explicit errors, and Gauss’s half-systems give an infinite family of non-Gorenstein orders with value semigroup ⟨3,5,7⟩; the discriminant splitting that links this to the gluing term is measured, not proved. | 📘 [open](https://karlesmarin.github.io/blueprints/s-matrix-orders-II/) · [`s-matrix-orders-II/`](s-matrix-orders-II/) | [10.5281/zenodo.22864266](https://doi.org/10.5281/zenodo.22864266) |
| ⚛️ | In the closed-form map of the SU(7) grand gauge-Higgs model of Komori and Maru, the inverse problem is decidable: a target (1/R₅, m_h) gets a bulk content or a named certificate that none exists; on the published seed the enumerated image is a finite set of points in clusters, nothing lies in (6.216, 8.897) TeV, and the two observables fix four of the five complete invariants on a rung but not the vacuum invariant W. | 📘 [open](https://karlesmarin.github.io/blueprints/su7-certified-gap/) · [`su7-certified-gap/`](su7-certified-gap/) | [10.5281/zenodo.22159036](https://doi.org/10.5281/zenodo.22159036) |
| ⚛️ | In the one-generation SU(7) grand gauge-Higgs model of Komori and Maru, anomaly cancellation forces the leftover U(1)′ to be T₃L + Y − (B − L), blind to every dimension-6 proton operator; the family-dependent escapes are classified inside their group, and at one-loop curvature only case (2) of their Table 1 can pay for them — a benchmark selected, not a model delivered. | 📘 [open](https://karlesmarin.github.io/blueprints/su7-proton-decay/) · [`su7-proton-decay/`](su7-proton-decay/) | [10.5281/zenodo.22033302](https://doi.org/10.5281/zenodo.22033302) |
| ⚖️ | Every length m ≡ 0, 3 (mod 4) is a zero of the weighted sum Σ n ε(n) for some completely multiplicative ε = ±1; the ε with infinitely many zeros form a dense G_δ of probability zero; quadratic characters give explicit ones through a digit recursion in base q, governed by the Euler factor at 2. | 📘 [open](https://karlesmarin.github.io/blueprints/weighted-partial-sums/) · [`weighted-partial-sums/`](weighted-partial-sums/) | [10.5281/zenodo.22847374](https://doi.org/10.5281/zenodo.22847374) |

## 🔗 Relation to the formalizations

`lean/` holds the source of the formalizations (from the public repository
[karlesmarin/formalizations](https://github.com/karlesmarin/formalizations)), shown in the library's 🔗 Lean view: every
module, every theorem, and the papers that use it.

## ➕ Adding a paper

The sites are built with Lemmario (part of the author's tools; not in this repository): one data file per paper, and
one command that rebuilds what is stale and this library. A paper enters only once it is published.

## 📜 License

Carles Marín (investigador independiente, karlesmarin@gmail.com).
Each blueprint copies its paper, under the paper's license (see its DOI); the Lean sources are Apache 2.0, as in
karlesmarin/formalizations. Written with Claude (Anthropic) as an AI assistant.
