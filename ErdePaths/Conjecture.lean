import ErdePaths.OddFrontiers

namespace ErdePaths.Conjecture

/-- The full even-hypercube path-decomposition statement. All odd frontiers
are constructed internally, then subdivided at every admissible length. -/
theorem erde_even_hypercube : ErdeEvenHypercubeConjecture :=
  Parameters.target_from_odd_frontiers OddFrontiers.frontiers

/-- Explicit quantified form of the same statement, using the faithful
binary-tuple cube representation and undirected simple-path partition. -/
theorem paths (n ℓ : Nat) (hn : 2≤n) (heven : n%2=0) (hℓ : 1≤ℓ)
    (hlt : ℓ<2^n) (hdiv : ℓ∣n*2^(n-1)) : HasPathDecomposition n ℓ :=
  erde_even_hypercube n ℓ hn heven hℓ hlt hdiv

#print axioms erde_even_hypercube
#print axioms paths
end ErdePaths.Conjecture
