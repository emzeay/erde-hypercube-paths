import ErdePaths.HamiltonNormalize

namespace ErdePaths.HamiltonCommonLast
open SourceClock SquareLift HamiltonData HamiltonNormalize

/-- Rotate every genuine factor while retaining actual edge partition data. -/
def rotateFactors {V R m N hN} (D : DecompositionData V R m N hN)
    (start : Fin m→Fin N) : DecompositionData V R m N hN where
  cycles i := rotate (D.cycles i) (start i)
  symmetric := D.symmetric
  loopfree := D.loopfree
  cover u v hv := by
    obtain ⟨i,t,ht⟩ := D.cover u v hv
    refine ⟨i,backward hN t (start i),?_⟩
    simpa only [rotate,forward_successor,forward_inverse] using ht
  unique i t j s he := by
    have hh : SameEdge
        ((D.cycles i).cycle (forward hN (start i) t),
          (D.cycles i).cycle (successor hN (forward hN (start i) t)))
        ((D.cycles j).cycle (forward hN (start j) s),
          (D.cycles j).cycle (successor hN (forward hN (start j) s))) := by
      simpa only [rotate,forward_successor] using he
    obtain ⟨hi,ht⟩ := D.unique _ _ _ _ hh
    refine ⟨hi,?_⟩
    subst j
    exact forward_injective hN (start i) ht

/-- Every actual H factor ends at the chosen common physical vertex. -/
def normalize {V R m N hN} (D : DecompositionData V R m N hN) (last : V) :
    DecompositionData V R m N hN :=
  rotateFactors D (fun i=>successor hN ((D.cycles i).position last))

theorem last_vertex {V R m N hN} (D : DecompositionData V R m N hN) (last : V) (i : Fin m) :
    ((normalize D last).cycles i).cycle ⟨N-1,by omega⟩=last := by
  change (D.cycles i).cycle
    (forward hN (successor hN ((D.cycles i).position last)) ⟨N-1,by omega⟩)=last
  rw [forward_last,predecessor_successor,(D.cycles i).cycle_position]

#print axioms rotateFactors
#print axioms last_vertex
end ErdePaths.HamiltonCommonLast
