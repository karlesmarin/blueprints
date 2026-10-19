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
| ⚖️ | Zeros of the weighted sums Σ_{n≤m} nε(n) of completely multiplicative ε with values ±1: every admissible length is a zero of some ε, infinitely many zeros are rare in measure and generic in category, and for quadratic characters the zeros are explicit. | 📘 [open](https://karlesmarin.github.io/blueprints/weighted-partial-sums/) · [`weighted-partial-sums/`](weighted-partial-sums/) | [10.5281/zenodo.22847374](https://doi.org/10.5281/zenodo.22847374) |

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
