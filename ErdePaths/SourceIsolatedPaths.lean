import ErdePaths.AACIsolatedOpening
import ErdePaths.SourceIsolatedGeometry

namespace ErdePaths.SourceIsolatedPaths
open SquareLift SourceClock AACTransition AACFineGeometry AACMarkIntervals SourceAACBase
attribute [local instance] Classical.propDecidable

/-- Both literal internal neighbors of an A=2 grid vertex are joined to
that common vertex by actual retained fine base edges. -/
theorem incident_edges {K B : Nat} {U W : Type} (hK : 0<K) (hB : 0<B)
    (G : ClockData U (K*2)) (H : ClockData W B)
    (i : Fin K) (j : Fin B) :
    GridHost hK (by decide : 0<2) hB G H
      (physical G H (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),j))
      (physical G H (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j)) ∧
    GridHost hK (by decide : 0<2) hB G H
      (physical G H (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),j))
      (physical G H (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j)) := by
  have hleft : successor (Nat.mul_pos hK (by decide : 0<2))
      (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2))=
      AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2) := by
    have hh (v : Fin K) : successor (Nat.mul_pos hK (by decide : 0<2))
        (AnchoredEmbedding.positionEncode v (⟨1,by decide⟩ : Fin 2))=
        AnchoredEmbedding.positionEncode (successor hK v) (⟨0,by decide⟩ : Fin 2) := by
      apply Fin.ext
      simp only [successor,AnchoredEmbedding.positionEncode,Nat.add_zero]
      change (2*v.val+1+1)%(K*2)=2*((v.val+1)%K)
      rw [show 2*v.val+1+1=(v.val+1)*2 by omega,Nat.mul_mod_mul_right]
      omega
    simpa only [successor_predecessor] using hh (predecessor hK i)
  have hright : successor (Nat.mul_pos hK (by decide : 0<2))
      (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2))=
      AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2) := by
    apply Fin.ext
    simp only [successor,AnchoredEmbedding.positionEncode,Nat.add_zero]
    have hi := i.isLt
    have hm := Nat.mul_le_mul_left 2 (show i.val+1≤K by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · refine ⟨Sum.inl (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j),Or.inr ?_⟩
    simp only [AACTransition.decode,hleft]
  · refine ⟨Sum.inl (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),j),Or.inl ?_⟩
    simp only [AACTransition.decode,hright]

theorem incident_edges_general {K A B : Nat} {U W : Type} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (G : ClockData U (K*A)) (H : ClockData W B) (i : Fin K) (j : Fin B)
    (z : Fin A) (hA2 : A=2) (hz : z.val=1) :
    GridHost hK hA hB G H (physical G H (AnchoredEmbedding.positionEncode i ⟨0,hA⟩,j))
      (physical G H (AnchoredEmbedding.positionEncode (predecessor hK i) z,j)) ∧
    GridHost hK hA hB G H (physical G H (AnchoredEmbedding.positionEncode i ⟨0,hA⟩,j))
      (physical G H (AnchoredEmbedding.positionEncode i z,j)) := by
  subst A
  have he : z=(⟨1,by decide⟩ : Fin 2) := Fin.ext hz
  subst z
  exact incident_edges hK hB G H i j

/-- Actual isolated-turn neighbor geometry after the EXACT first-mark cut.
The source coefficient and row are uniform; no geometric witness is input. -/
theorem ordinary_geometry (I : SourceLocalFold.Input) (hr : I.r=1)
    (short : I.b≤2^(I.a+I.h+1-I.r)-3) (f : I.Index) :
    ∃a b : Fin I.E, ∃u : I.Y,
      I.flag f a=false ∧ I.flag f b=false ∧
      (∀p,I.base f p=I.base f a→p=a) ∧ (∀p,I.base f p=I.base f b→p=b) ∧
      I.color f a≠I.color f b ∧ I.Host f u (I.base f a) ∧ I.Host f u (I.base f b) := by
  let K := 2^(I.e*2^(I.a+I.h+1)-I.r)
  let i : Fin K := ⟨I.b+1,by
    have hd := SourceLengths.coarse_period I.he I.a I.h I.r I.hr
    have hperiod := Nat.le_of_dvd (Nat.two_pow_pos (I.e*2^(I.a+I.h+1)-I.r)) hd
    have hs := I.short
    omega⟩
  let G := SourceAACBase.G I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance I.z (I.factor f)
  let H := SourceAACBase.H I.a I.h I.r I.hr I.HD I.last (I.factor f)
  obtain ⟨p,q,hp,hq,hpu,hqu,hpf,hqf,hc⟩ := SourceIsolatedGeometry.ordinary_neighbors I hr short f
  let a := backward I.epos p (I.first f)
  let b := backward I.epos q (I.first f)
  have ha := AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase f) I.originalColor
    (I.first f) p hpf hpu
  have hb := AACIsolatedOpening.rotate_occurrence I.epos (I.originalBase f) I.originalColor
    (I.first f) q hqf hqu
  let u := physical G H (AnchoredEmbedding.positionEncode i ⟨0,Nat.two_pow_pos I.r⟩,
    SourceIsolatedGeometry.lastRow I.hB)
  have hz : I.z.val=1 := by
    have hh := I.hz
    have hi := I.z.isLt
    simp only [hr,Nat.pow_one] at hi
    omega
  have hedges := incident_edges_general (Nat.two_pow_pos _) (Nat.two_pow_pos _) I.hB G H i
    (SourceIsolatedGeometry.lastRow I.hB) I.z (by simp only [hr,Nat.pow_one]) hz
  have heleft : I.Host f u (I.originalBase f p) := by
    rw [hp]
    exact (SourceAACBase.gridHost_source I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance
      I.HD I.last I.z (I.factor f) _ _).mp hedges.1
  have heright : I.Host f u (I.originalBase f q) := by
    rw [hq]
    exact (SourceAACBase.gridHost_source I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance
      I.HD I.last I.z (I.factor f) _ _).mp hedges.2
  refine ⟨a,b,u,ha.2.2.1,hb.2.2.1,ha.2.2.2,hb.2.2.2,?_,?_,?_⟩
  · change I.originalColor (forward I.epos (I.first f) a)≠I.originalColor (forward I.epos (I.first f) b)
    rw [forward_inverse,forward_inverse]
    exact hc
  · change I.Host f u (I.originalBase f (forward I.epos (I.first f) a))
    rw [forward_inverse]
    exact heleft
  · change I.Host f u (I.originalBase f (forward I.epos (I.first f) b))
    rw [forward_inverse]
    exact heright

/-- Unconditional A=2 ordinary-source local opening, at the real fold
length and host, without neighbor/fork/return/partition premises. -/
noncomputable def paths {X : Type} {R : X→X→Prop} {χ : X→Bool} {jR : Nat} (hj : 0<jR)
    (I : SourceLocalFold.Input) (hr : I.r=1) (short : I.b≤2^(I.a+I.h+1-I.r)-3) (h2 : 2≤jR)
    (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj) (f : I.Index) :
    GraphPathDecomposition (I.Y×X)
      (AACFoldEdgeLedger.InputHost (I.Host f) (I.flag f) (I.base f) (I.layers hj cycles f))
      (I.length (jR:=jR) f) := by
  let a := Classical.choose (ordinary_geometry I hr short f)
  have ha0 := Classical.choose_spec (ordinary_geometry I hr short f)
  let b := Classical.choose ha0
  have hb0 := Classical.choose_spec ha0
  let u := Classical.choose hb0
  have hu := Classical.choose_spec hb0
  exact AACIsolatedOpening.source_paths hj I h2 cycles f a b hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1
    hu.2.2.2.2.1 u hu.2.2.2.2.2.1 hu.2.2.2.2.2.2

#print axioms ordinary_geometry
#print axioms paths
#print axioms incident_edges
end ErdePaths.SourceIsolatedPaths
