import ErdePaths.QuarterAACBase
import ErdePaths.SourceIsolatedPaths

namespace ErdePaths.QuarterIsolatedPaths
open SquareLift SourceClock QuarterAACBase AACFineGeometry PairedLayers
attribute [local instance] Classical.propDecidable

/-- Actual original quarter neighbors at column one in flipped row zero;
the common physical grid anchor and its incident edges are derived. -/
theorem original_geometry (I : Input) (n : I.Index) :
    ∃a b : Fin I.E, ∃u : I.Y,
      I.originalFlag a=false ∧ I.originalFlag b=false ∧
      (∀p,I.originalBase n p=I.originalBase n a→p=a) ∧
      (∀p,I.originalBase n p=I.originalBase n b→p=b) ∧
      I.originalColor a≠I.originalColor b ∧
      I.Host n u (I.originalBase n a) ∧ I.Host n u (I.originalBase n b) := by
  have hk : 4≤I.K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period I.he)
  let i : Fin I.K := ⟨1,by omega⟩
  obtain ⟨a,b,ha,hb,hua,hub,hfa,hfb,hc⟩ := QuarterPatternGeometry.zero_row_neighbors
    (Nat.two_pow_pos _) I.hB (QuarterPhysicalIncidence.period I.he) I.hB4 I.evenB (I.G n) (I.H n)
  let u := physical (I.G n) (I.H n) (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),⟨0,I.hB⟩)
  have he := SourceIsolatedPaths.incident_edges (Nat.two_pow_pos _) I.hB (I.G n) (I.H n) i ⟨0,I.hB⟩
  change I.originalBase n a=physical (I.G n) (I.H n)
    (AnchoredEmbedding.positionEncode (predecessor (Nat.two_pow_pos _) i) (⟨1,by decide⟩ : Fin 2),⟨0,I.hB⟩) at ha
  change I.originalBase n b=physical (I.G n) (I.H n)
    (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),⟨0,I.hB⟩) at hb
  have hleft : I.Host n u (I.originalBase n a) := by
    rw [ha]
    exact (QuarterFactorGeometry.grid_host_iff I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
      (⟨1,by decide⟩ : Fin 2) (I.factor n) _ _).mp he.1
  have hright : I.Host n u (I.originalBase n b) := by
    rw [hb]
    exact (QuarterFactorGeometry.grid_host_iff I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
      (⟨1,by decide⟩ : Fin 2) (I.factor n) _ _).mp he.2
  exact ⟨a,b,u,hfa,hfb,hua,hub,hc,hleft,hright⟩

theorem geometry (I : Input) (n : I.Index) :
    ∃a b : Fin I.E, ∃u : I.Y,
      I.flag n a=false ∧ I.flag n b=false ∧
      (∀p,I.base n p=I.base n a→p=a) ∧ (∀p,I.base n p=I.base n b→p=b) ∧
      I.color n a≠I.color n b ∧ I.Host n u (I.base n a) ∧ I.Host n u (I.base n b) := by
  obtain ⟨p,q,u,hp,hq,hpu,hqu,hc,hea,heb⟩ := original_geometry I n
  let a := backward I.epos p (I.first n)
  let b := backward I.epos q (I.first n)
  have ha := AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase n) I.originalColor (I.first n) p hp hpu
  have hb := AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase n) I.originalColor (I.first n) q hq hqu
  refine ⟨a,b,u,ha.2.2.1,hb.2.2.1,ha.2.2.2,hb.2.2.2,?_,?_,?_⟩
  · change I.originalColor (forward I.epos (I.first n) a)≠I.originalColor (forward I.epos (I.first n) b)
    rw [forward_inverse,forward_inverse]
    exact hc
  · change I.Host n u (I.originalBase n (forward I.epos (I.first n) a))
    rw [forward_inverse]
    exact hea
  · change I.Host n u (I.originalBase n (forward I.epos (I.first n) b))
    rw [forward_inverse]
    exact heb

section Fold
variable {X : Type} {R : X→X→Prop} {χ : X→Bool} {jR : Nat} (hj : 0<jR)

private theorem pair_of_geometry (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*1)→CycleData X R χ jR hj) (n : I.Index)
    (a b : Fin I.E) (ha : I.flag n a=false) (hb : I.flag n b=false)
    (hua : ∀p,I.base n p=I.base n a→p=a) (hub : ∀p,I.base n p=I.base n b→p=b)
    (hc : I.color n a≠I.color n b) (u : I.Y)
    (hea : I.Host n u (I.base n a)) (heb : I.Host n u (I.base n b)) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=jR) n),
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) v w := by
  have hword := I.word_length n
  have hlength := (I.decomposition hj h2 cycles n).2.2.2.2
  have hlarge : 3≤I.length (jR:=jR) n := by
    rw [hlength]
    have hm := Nat.mul_le_mul h2 (show 4≤I.E+(I.marks.word n).length by omega)
    omega
  have hreturn := AACFoldEdgeLedger.forest_return (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)
  let x := (cycles (I.schedule.active n)).vertex (⟨0,hj⟩,false)
  have hea' : AACFoldEdgeLedger.HostAdjacent I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (u,x) (I.base n a,x) :=
    (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (I.Host n) (I.host_cover n) _ _).mpr (Or.inl ⟨rfl,hea⟩)
  have heb' : AACFoldEdgeLedger.HostAdjacent I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (u,x) (I.base n b,x) :=
    (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (I.Host n) (I.host_cover n) _ _).mpr (Or.inl ⟨rfl,heb⟩)
  obtain ⟨P,hP⟩ := AACIsolatedOpening.isolated_fork I.epos h2 (I.base n) (I.color n) (I.cut_mark n)
    (I.mark_unique n) (I.collision n) (cycles (I.schedule.active n)) (I.layers hj cycles n)
    (I.selectors hj cycles n) (I.qpos n) hreturn (I.edge_unique n) hlarge
    a b ha hb hua hub hc u x hea' heb'
  refine ⟨P,?_⟩
  intro v w
  exact (hP v w).trans (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n)
    (I.layers hj cycles n) (I.Host n) (I.host_cover n) v w)

theorem pair (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=jR) n),
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) v w := by
  obtain ⟨a,b,u,ha,hb,hua,hub,hc,hea,heb⟩ := geometry I n
  exact pair_of_geometry hj I h2 cycles n a b ha hb hua hub hc u hea heb

noncomputable def paths (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    GraphPathDecomposition (I.Y×X)
      (AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n) (I.layers hj cycles n))
      (I.length (jR:=jR) n) := by
  let P := Classical.choose (pair hj I h2 cycles n)
  have hP := Classical.choose_spec (pair hj I h2 cycles n)
  let D := P.decomposition
  exact {
    Index:=D.Index, indices:=D.indices, vertices:=D.vertices, simple:=D.simple
    adjacent:=fun p hp k=>(hP _ _).mp (D.adjacent p hp k)
    cover:=fun v w hh=>D.cover v w ((hP v w).mpr hh)
    unique:=D.unique }
end Fold
#print axioms paths
#print axioms pair
#print axioms geometry
#print axioms original_geometry
end ErdePaths.QuarterIsolatedPaths
