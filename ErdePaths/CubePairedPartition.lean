import ErdePaths.HamiltonCommonLast
import ErdePaths.CubeCycle
import ErdePaths.AACFoldEdgeLedger
import ErdePaths.SourceHostPartition

namespace ErdePaths.CubePairedPartition
open SquareLift CubeParity HamiltonData LayerOwnership SubdividedWiggle

/-- Both actual alternating matchings exhaust exactly a numeric cycle's
undirected edges; no matching coverage premise is supplied. -/
theorem paired_iff {n r : Nat} (hr : 0<r)
    (C : HamiltonData.CycleData (Vertex n) (@Adjacent n) (2*r) (by omega))
    (hzero : parity (C.cycle ⟨0,by omega⟩)=false) (u v : Vertex n) :
    AACFoldEdgeLedger.CycleAdjacent (CubeCycle.paired hr C hzero) u v ↔
      ∃i, SameEdge (C.cycle i,C.cycle (successor (by omega) i)) (u,v) := by
  constructor
  · rintro ⟨a,t,he⟩
    cases a
    · refine ⟨CubeCycle.index hr (t,false),?_⟩
      rw [CubeCycle.index_even_next]
      simp only [matchingPair,choose,Bool.false_eq_true,ite_false,
        PairedLayers.matchingA_vertex,Bool.not_false] at he
      exact he
    · refine ⟨CubeCycle.index hr (PairedLayers.previous hr t,true),?_⟩
      rw [CubeCycle.index_odd_next,PairedLayers.next_previous]
      have hm : matchingPair (CubeCycle.paired hr C hzero) true t=
          (C.cycle (CubeCycle.index hr (t,false)),C.cycle (CubeCycle.index hr (PairedLayers.previous hr t,true))) := by
        simp only [matchingPair,choose,↓reduceIte,PairedLayers.matchingB_even]
        rfl
      rw [hm] at he
      exact sameEdge_trans (Or.inr rfl) he
  · rintro ⟨i,he⟩
    let p := CubeCycle.coordinates hr i
    have hi : CubeCycle.index hr p=i := CubeCycle.index_coordinates hr i
    rw [←hi] at he
    rcases p with ⟨t,b⟩
    cases b
    · refine ⟨false,t,?_⟩
      rw [CubeCycle.index_even_next] at he
      simp only [matchingPair,choose,Bool.false_eq_true,ite_false,
        PairedLayers.matchingA_vertex,Bool.not_false]
      exact he
    · refine ⟨true,successor hr t,?_⟩
      rw [CubeCycle.index_odd_next] at he
      have hm : matchingPair (CubeCycle.paired hr C hzero) true (successor hr t)=
          (C.cycle (CubeCycle.index hr (successor hr t,false)),C.cycle (CubeCycle.index hr (t,true))) := by
        simp only [matchingPair,choose,↓reduceIte,PairedLayers.matchingB_even,PairedLayers.previous_next]
        rfl
      rw [hm]
      exact sameEdge_trans (Or.inr rfl) he

section Partition
variable {n m r : Nat} (hr : 0<r)
  (D : DecompositionData (Vertex n) (@Adjacent n) m (2*r) (by omega))

def zeroFactors : DecompositionData (Vertex n) (@Adjacent n) m (2*r) (by omega) :=
  HamiltonCommonLast.rotateFactors D (fun i=>(D.cycles i).position ⟨0,Nat.two_pow_pos n⟩)

def cycles (i : Fin m) : PairedLayers.CycleData (Vertex n) (@Adjacent n) parity r hr :=
  CubeCycle.pairedCube hr (D.cycles i)

/-- Actual paired layer-cycle edges are exactly edges of the retained genuine
Hamilton partition, at its derived all-zero origins. -/
theorem cycles_iff (i : Fin m) (u v : Vertex n) :
    AACFoldEdgeLedger.CycleAdjacent (cycles hr D i) u v ↔
      SourceHostPartition.FactorEdge (zeroFactors hr D) i u v := by
  exact paired_iff hr (CubeCycle.atZero (by omega) (D.cycles i))
    (CubeCycle.atZero_origin (by omega) (D.cycles i)) u v

theorem cover (u v : Vertex n) (he : Adjacent u v) :
    ∃i, AACFoldEdgeLedger.CycleAdjacent (cycles hr D i) u v := by
  obtain ⟨i,t,ht⟩ := (zeroFactors hr D).cover u v he
  exact ⟨i,(cycles_iff hr D i u v).mpr ⟨t,ht⟩⟩

theorem relation {i : Fin m} {u v : Vertex n}
    (he : AACFoldEdgeLedger.CycleAdjacent (cycles hr D i) u v) : Adjacent u v :=
  SourceHostPartition.factorEdge_relation _ ((cycles_iff hr D i u v).mp he)

theorem unique {i j : Fin m} {u v : Vertex n}
    (hi : AACFoldEdgeLedger.CycleAdjacent (cycles hr D i) u v)
    (hj : AACFoldEdgeLedger.CycleAdjacent (cycles hr D j) u v) : i=j :=
  SourceHostPartition.factorEdge_unique _ ((cycles_iff hr D i u v).mp hi) ((cycles_iff hr D j u v).mp hj)

end Partition
#print axioms paired_iff
#print axioms cover
#print axioms unique
end ErdePaths.CubePairedPartition
