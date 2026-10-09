# Erde’s Even-Hypercube Path-Decomposition Conjecture

Lean 4 formalization of **Conjecture 8** in Joshua Erde’s [*Decomposing the cube into paths*, arXiv:1310.6776v1](https://arxiv.org/abs/1310.6776v1).

**Provisional research release.** This repository contains the complete formal proof and a mathematical exposition. The formalization has been checked locally with Lean’s kernel. Independent mathematical review has not been completed.

**AI disclosure.** This project was developed with AI assistance, including mathematical research, Lean formalization, and documentation. [PROOF.md](PROOF.md) is an AI-generated prose argument explaining the formal proof. Lean’s kernel checks the formalization; the prose argument requires separate mathematical review. I plan to release a revised proof exposition with more of my own mathematical development and writing.

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
```

`lean-toolchain` pins Lean **4.34.1**. The project uses Lean’s bundled standard library and has no external Lake dependencies. The second command prints the final theorem’s transitive axioms:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean axioms. No `sorry`, admitted result, custom conjecture axiom, or `native_decide` is used in the proof. Kernel checking establishes the formal statement under these axioms; it does not establish research novelty or replace review of the definitions and exposition.

## Reading the proof

Start with [PROOF.md](PROOF.md) for the mathematical argument and its module map. For a short route through the formalization:

1. [Basic.lean](ErdePaths/Basic.lean) and [Binary.lean](ErdePaths/Binary.lean) define the cube, simple paths and unique undirected edge ownership, and establish the binary-tuple representation.
2. [EvenHamilton.lean](ErdePaths/EvenHamilton.lean), [SourceUniformPaths.lean](ErdePaths/SourceUniformPaths.lean), and [MersenneUniformPaths.lean](ErdePaths/MersenneUniformPaths.lean) provide uniform constructions. PROOF.md explains their supporting mechanisms and the necessary two-bit, isolated and zero-depth branches.
3. [OddFrontiers.lean](ErdePaths/OddFrontiers.lean) combines all positive odd coefficients, with unrestricted binary complexity and dimension multiplier.
4. [Parameters.lean](ErdePaths/Parameters.lean) and [Subdivision.lean](ErdePaths/Subdivision.lean) reduce every admissible length to those frontiers. [Conjecture.lean](ErdePaths/Conjecture.lean) concludes the full statement without a supplied construction hypothesis.

## License

Source and documentation are licensed under the [Apache License, Version 2.0](LICENSE).
