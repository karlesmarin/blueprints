# 📚 Blueprints

🌐 **[Open the library](https://karlesmarin.github.io/blueprints/)**

What each paper proves, how its results depend on each other, and what exactly has been checked. The published companion sites (blueprints) of Carles Marín's papers, with the library page that
indexes them: every statement copied verbatim with the paper's numbering, what it uses and where it is used, and what
was checked besides the written proof.

- 📄 Published versions only: each blueprint follows the version named on its card (DOI), and carries that PDF.
- ✅ What is checked is said statement by statement: 🔗 Lean (linked to karlesmarin/formalizations), 💻 programs,
  🔍 audits.
- 🎬 The paper's figures come alive (3D, sliders), and 🧪 the labs run the paper's own code in the browser.
- 🤖 Generated: do not edit by hand.

## 🚀 Using it

Open [the library](https://karlesmarin.github.io/blueprints/). Or locally:

```
git clone https://github.com/karlesmarin/blueprints.git
cd blueprints
python -m http.server
```

and open `http://localhost:8000/`.

## 🗂️ Contents

| | Paper | Folder | Version |
|---|---|---|---|
| 💠 | The irreducible characters of Sp(2m) at every power of Kostant's element: when they vanish, their value as a signed ratio of root products, and their absolute value as a product of dimensions of GL, Sp and odd SO representations. | [`characters-at-aP/`](characters-at-aP/) | [10.5281/zenodo.22683560](https://doi.org/10.5281/zenodo.22683560) |
| ⚖️ | Zeros of the weighted sums Σ_{n≤m} nε(n) of completely multiplicative ε with values ±1: every admissible length is a zero of some ε, infinitely many zeros are rare in measure and generic in category, and for quadratic characters the zeros are explicit. | [`weighted-partial-sums/`](weighted-partial-sums/) | [10.5281/zenodo.22847374](https://doi.org/10.5281/zenodo.22847374) |

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
