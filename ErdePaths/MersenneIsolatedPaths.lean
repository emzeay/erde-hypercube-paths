import ErdePaths.AACIsolatedOpening
import ErdePaths.MersenneAACBase
import ErdePaths.SourceIsolatedPaths
import ErdePaths.SourceIsolatedGeometry

namespace ErdePaths.MersenneIsolatedPaths
open SquareLift MersenneAACBase
attribute [local instance] Classical.propDecidable

/-- Actual literal long-word neighbors, transported through the genuine
first-mark cut and joined to the actual common grid vertex. -/
theorem geometry (I : Input) (n : I.Index) :
    ∃(u : I.Y) (a b : Fin I.E),
      I.flag n a=false ∧ I.flag n b=false ∧
      (∀p,I.base n p=I.base n a→p=a) ∧
      (∀p,I.base n p=I.base n b→p=b) ∧
      I.color n a≠I.color n b ∧
      I.Host n u (I.base n a) ∧ I.Host n u (I.base n b) := by
  let K:=2^(I.e*2^(I.k+I.h+1)-1)
  let P:=2^(I.k+I.h+1)
  have hd:=SourceIsolatedGeometry.long_period I.he I.k I.h
  have hl : 2*P≤K := Nat.le_of_dvd (Nat.two_pow_pos _) hd
  have hP : 8≤P := Nat.pow_le_pow_right (by decide : 1≤2)
    (show 3≤I.k+I.h+1 by have := I.hk; omega)
  let i : Fin K:=⟨P+3,by omega⟩
  let G:=MersenneAACBase.G I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance I.exceptional I.z (I.factor n)
  let H:=MersenneAACBase.H I.k I.h I.hk I.HD I.last (I.factor n)
  let j:=SourceIsolatedGeometry.lastRow I.hB
  have hp:=SourceIsolatedGeometry.mersenne_neighbors I n
  change ∃a b : Fin I.E,
    I.originalBase n a=AACFineGeometry.physical G H
      (AnchoredEmbedding.positionEncode (predecessor (Nat.two_pow_pos _) i) (⟨1,by decide⟩ : Fin 2),j) ∧
    I.originalBase n b=AACFineGeometry.physical G H
      (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) ∧
    (∀p,I.originalBase n p=I.originalBase n a→p=a) ∧
    (∀p,I.originalBase n p=I.originalBase n b→p=b) ∧
    I.originalFlag a=false ∧ I.originalFlag b=false ∧ I.originalColor a≠I.originalColor b at hp
  obtain ⟨a,b,ha,hb,hua,hub,hfa,hfb,hc⟩:=hp
  have hra:=AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase n) I.originalColor
    (I.first n) a hfa hua
  have hrb:=AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase n) I.originalColor
    (I.first n) b hfb hub
  let aa:=backward I.epos a (I.first n)
  let bb:=backward I.epos b (I.first n)
  have hav : I.base n aa=I.originalBase n a:=hra.1
  have hbv : I.base n bb=I.originalBase n b:=hrb.1
  let u:=AACFineGeometry.physical G H (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),j)
  have he:=SourceIsolatedPaths.incident_edges (Nat.two_pow_pos _) I.hB G H i j
  have hleft : I.Host n u (I.base n aa) := by
    rw [hav,ha]
    exact (MersenneAACBase.gridHost_source I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance
      I.exceptional I.HD I.last I.z (I.factor n) _ _).mp he.1
  have hright : I.Host n u (I.base n bb) := by
    rw [hbv,hb]
    exact (MersenneAACBase.gridHost_source I.D I.he I.k I.h I.hk I.hh I.room I.S I.ho I.balance
      I.exceptional I.HD I.last I.z (I.factor n) _ _).mp he.2
  refine ⟨u,aa,bb,hra.2.2.1,hrb.2.2.1,hra.2.2.2,hrb.2.2.2,?_,hleft,hright⟩
  have hac : I.color n aa=I.originalColor a:=hra.2.1
  have hbc : I.color n bb=I.originalColor b:=hrb.2.1
  rw [hac,hbc]
  exact hc

section Fold
variable {X : Type} {R : X→X→Prop} {χ : X→Bool} {jR : Nat} (hj : 0<jR)

/-- Internal instantiation of the generic isolated fork. Only actual input
neighbor data occur at this private helper; the public construction derives
them from the literal long word. -/
private theorem pair_of_geometry (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*(2^(I.k+I.h)-1))→PairedLayers.CycleData X R χ jR hj) (n : I.Index)
    (a b : Fin I.E) (ha : I.flag n a=false) (hb : I.flag n b=false)
    (hua : ∀p,I.base n p=I.base n a→p=a) (hub : ∀p,I.base n p=I.base n b→p=b)
    (hc : I.color n a≠I.color n b) (u : I.Y)
    (hea : I.Host n u (I.base n a)) (heb : I.Host n u (I.base n b)) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=jR) n),
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) v w := by
  have hword := MersenneAACBase.global_word_length I.branch I.D I.hh I.room I.S I.ho I.balance
    I.hB I.hB4 I.evenB I.HD I.last I.z I.hz n
  change 4≤(I.marks.word n).length at hword
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
/-- Every actual Mersenne input and its genuinely assigned layer cycles
supply an exact normalized local fork; no geometry/output premise remains. -/
theorem pair (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*(2^(I.k+I.h)-1))→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=jR) n),
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) v w := by
  obtain ⟨u,a,b,ha,hb,hua,hub,hc,hea,heb⟩:=geometry I n
  exact pair_of_geometry hj I h2 cycles n a b ha hb hua hub hc u hea heb

/-- Two actual simple paths of the full folded length partition the exact
original local Mersenne marked host. Geometry, schedule return and edge
ownership are all derived from the actual constructed input. -/
noncomputable def paths (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*(2^(I.k+I.h)-1))→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    GraphPathDecomposition (I.Y×X)
      (AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n) (I.layers hj cycles n))
      (I.length (jR:=jR) n) := by
  let P:=Classical.choose (pair hj I h2 cycles n)
  have hP:=Classical.choose_spec (pair hj I h2 cycles n)
  let D:=P.decomposition
  exact {
    Index:=D.Index, indices:=D.indices, vertices:=D.vertices, simple:=D.simple
    adjacent:=fun p hp j=>(hP _ _).mp (D.adjacent p hp j)
    cover:=fun v w hh=>D.cover v w ((hP v w).mpr hh)
    unique:=D.unique }

end Fold
#print axioms geometry
#print axioms pair
#print axioms paths
end ErdePaths.MersenneIsolatedPaths
