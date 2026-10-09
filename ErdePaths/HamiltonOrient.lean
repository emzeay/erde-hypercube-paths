import ErdePaths.OrientedClock

namespace ErdePaths.HamiltonOrient
open SourceClock SquareLift HamiltonData HamiltonNormalize OrientedClock

def edgeIndex {N} (hN : 0<N) (start : Fin N) (eps : Bool) (t : Fin N) : Fin N :=
  if eps then forward hN start t else backward hN start (successor hN t)

theorem edgeIndex_injective {N} (hN : 0<N) (start : Fin N) (eps : Bool) :
    Function.Injective (edgeIndex hN start eps) := by
  intro t s he
  cases eps
  · have hh := backward_injective hN start he
    have hp := congrArg (predecessor hN) hh
    simpa only [predecessor_successor] using hp
  · exact forward_injective hN start he

theorem edgeIndex_surjective {N} (hN : 0<N) (start : Fin N) (eps : Bool) :
    Function.Surjective (edgeIndex hN start eps) := by
  intro t
  cases eps
  · exact ⟨predecessor hN (backward hN start t),by
      simp only [edgeIndex,Bool.false_eq_true,ite_false,successor_predecessor,backward_inverse]⟩
  · exact ⟨backward hN t start,by
      simp only [edgeIndex,ite_true,forward_inverse]⟩

/-- Each actual oriented edge has a unique old physical edge index. -/
theorem edge_same {V R N hN} (C : CycleData V R N hN) (hs : ∀u v,R u v→R v u)
    (start : Fin N) (eps : Bool) (t : Fin N) :
    SameEdge (((OrientedClock.cycle C hs start eps).cycle t),
      ((OrientedClock.cycle C hs start eps).cycle (successor hN t)))
      (C.cycle (edgeIndex hN start eps t),C.cycle (successor hN (edgeIndex hN start eps t))) := by
  cases eps
  · change SameEdge (C.cycle (backward hN start t),C.cycle (backward hN start (successor hN t)))
      (C.cycle (backward hN start (successor hN t)),C.cycle (successor hN (backward hN start (successor hN t))))
    rw [reverse_step]
    exact Or.inr rfl
  · change SameEdge (C.cycle (forward hN start t),C.cycle (forward hN start (successor hN t)))
      (C.cycle (forward hN start t),C.cycle (successor hN (forward hN start t)))
    rw [forward_successor]
    exact Or.inl rfl

/-- Arbitrary actual factor rotations and reversals retain the complete
physical Hamilton edge partition, not only each factor's adjacency. -/
def factors {V R m N hN} (D : DecompositionData V R m N hN)
    (start : Fin m→Fin N) (eps : Fin m→Bool) : DecompositionData V R m N hN where
  cycles i := OrientedClock.cycle (D.cycles i) D.symmetric (start i) (eps i)
  symmetric := D.symmetric
  loopfree := D.loopfree
  cover u v hv := by
    obtain ⟨i,t,ht⟩ := D.cover u v hv
    obtain ⟨s,hs⟩ := edgeIndex_surjective hN (start i) (eps i) t
    refine ⟨i,s,?_⟩
    have he := edge_same (D.cycles i) D.symmetric (start i) (eps i) s
    rw [hs] at he
    exact sameEdge_trans he ht
  unique i t j s he := by
    have hi := edge_same (D.cycles i) D.symmetric (start i) (eps i) t
    have hj := edge_same (D.cycles j) D.symmetric (start j) (eps j) s
    have hh := sameEdge_trans (sameEdge_symm hi) (sameEdge_trans he hj)
    obtain ⟨hij,hts⟩ := D.unique _ _ _ _ hh
    refine ⟨hij,?_⟩
    subst j
    exact edgeIndex_injective hN (start i) (eps i) hts

#print axioms factors
end ErdePaths.HamiltonOrient
