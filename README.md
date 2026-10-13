# Erde’s Even-Hypercube Path-Decomposition Conjecture

Lean 4 formalization of **Conjecture 8** in Joshua Erde’s [*Decomposing the cube into paths*, arXiv:1310.6776v1](https://arxiv.org/abs/1310.6776v1).

**Provisional research release.** This repository contains the complete formal proof and a mathematical exposition. The formalization has been checked locally with Lean’s kernel. External independent mathematical review has *not* been completed.

**Reading the result.** The curated manuscript in [paper.pdf](paper.pdf) presents the proof and its consequences. The AI-generated exposition in [proof-ai-generated.md](proof-ai-generated.md) gives a searchable Markdown account of both, with a map to the Lean modules.

**AI disclosure.** This project was developed with AI assistance from OpenAI’s Codex in mathematical research, Lean formalization, and initial drafting. The manuscript incorporates substantial human revision, curation, and checking of the argument. The Markdown exposition is almost entirely AI-generated.

## Statement

For every even integer $n\geq 2$ and every integer $\ell\geq 1$ satisfying

$$
\ell<2^n \qquad\text{and}\qquad \ell\mid n2^{n-1},
$$

the edges of the hypercube $Q_n$ can be partitioned into simple paths, each having exactly $\ell$ edges. Vertices are binary $n$-tuples, and adjacency means differing in exactly one coordinate. Different paths may share vertices.

The final declarations are `ErdePaths.Conjecture.erde_even_hypercube` and `ErdePaths.Conjecture.paths` in [Conjecture.lean](ErdePaths/Conjecture.lean). The latter states the hypotheses explicitly:

```lean
theorem paths (n ℓ : Nat) (hn : 2≤n) (heven : n%2=0) (hℓ : 1≤ℓ)
    (hlt : ℓ<2^n) (hdiv : ℓ∣n*2^(n-1)) : HasPathDecomposition n ℓ
```

## Verification

Install [Lean and its toolchain manager, elan](https://lean-lang.org/install/). From the repository root, run:

```sh
lake build
lake env lean --trust=0 ErdePaths/Conjecture.lean
lake env lean --trust=0 ErdePaths/Consequences/ProductTransfer.lean
lake env lean --trust=0 ErdePaths/Consequences/Optimization.lean
```

The toolchain configuration pins Lean **4.34.1**. The project uses Lean’s bundled standard library and has no external Lake dependencies. The core-theorem command prints its transitive axioms:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean axioms. No `sorry`, admitted result, custom conjecture axiom, or `native_decide` is used in the proof. Kernel checking establishes the formal statement under these axioms but it does not replace independent mathematical review of the definitions and exposition.

## Reading the proof

Start with the curated manuscript in [paper.pdf](paper.pdf) or the AI-generated exposition in [proof-ai-generated.md](proof-ai-generated.md). For a short route through the formalization:

1. [Basic.lean](ErdePaths/Basic.lean) and [Binary.lean](ErdePaths/Binary.lean) define the cube, simple paths and unique undirected edge ownership, and establish the binary-tuple representation.
2. [EvenHamilton.lean](ErdePaths/EvenHamilton.lean), [SourceUniformPaths.lean](ErdePaths/SourceUniformPaths.lean), and [MersenneUniformPaths.lean](ErdePaths/MersenneUniformPaths.lean) provide uniform constructions. The Markdown exposition explains their supporting mechanisms and the necessary two-bit, isolated and zero-depth branches.
3. [OddFrontiers.lean](ErdePaths/OddFrontiers.lean) combines all positive odd coefficients, with unrestricted binary complexity and dimension multiplier.
4. [Parameters.lean](ErdePaths/Parameters.lean) and [Subdivision.lean](ErdePaths/Subdivision.lean) reduce every admissible length to those frontiers. [Conjecture.lean](ErdePaths/Conjecture.lean) concludes the full statement without a supplied construction hypothesis.

## Consequences and formal scope

The manuscript and Markdown exposition include optimal equal-length path counts, the structure of certain optimal decompositions, and transfers to even-alphabet Hamming graphs, products of even cycles, and equally regular bipartite products.

The product-transfer module in [Consequences/ProductTransfer.lean](ErdePaths/Consequences/ProductTransfer.lean) fully formalizes the graph-transfer existence statements, including simplicity and exact edge ownership. The optimization module in [Consequences/Optimization.lean](ErdePaths/Consequences/Optimization.lean) checks the supporting arithmetic, capacity bounds, and local incidence implications. Global counting arguments, the minimum over all equal-length decompositions, and global omitted-block counts remain prose. These supplementary boundaries do not affect the complete core theorem. Both consequence modules are included in `lake build`. Their declaration namespaces are `ErdePaths.Consequences.ProductTransfer` and `ErdePaths.Consequences.Optimization`, respectively.

## License

Source and documentation are licensed under the [Apache License, Version 2.0](LICENSE).
