import ErdePaths.SourceLocalFold
import ErdePaths.AACFoldFork

namespace ErdePaths.SourceFork
open SquareLift SourceClock AACMarkIntervals AACIntervalSplit AACFineClock
open SourceLocalFold
attribute [local instance] Classical.propDecidable

/-- Literal postcut neighbors of every real buffered mark are unmarked and
physically unique, derived from the actual fine Euler traversal. -/
theorem buffered_neighbors (I : Input) (hr : 2≤I.r) (hz : I.z.val=2)
    (n : I.Index) (p q : Fin I.E) (hp : I.flag n p=true)
    (hq : q=successor I.epos p ∨ q=predecessor I.epos p) :
    I.flag n q=false ∧ ∀v,I.base n v=I.base n q→v=q := by
  let K := 2^(I.e*2^(I.a+I.h+1)-I.r)
  let A := 2^I.r
  let E := SourceChronologicalMarks.sourceEuler (b:=I.b) I.he I.a I.h I.r I.hr I.hB
  let G := SourceAACBase.G I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance I.z (I.factor n)
  let H := SourceAACBase.H I.a I.h I.r I.hr I.HD I.last (I.factor n)
  have hA4 : 4≤A := Nat.pow_le_pow_right (show 1≤2 by decide) hr
  have hK4 : 4≤K := SourceLengths.coarse_size I.he I.a I.h I.r I.hr
  have h3 : 3≤K*A := by
    have hm := Nat.mul_le_mul_left K (show 1≤A from Nat.two_pow_pos I.r)
    simp only [Nat.mul_one] at hm
    omega
  have hE2 : 2≤I.E := by
    have hBA : 1≤I.B*(A+1) := Nat.mul_pos I.hB (by omega)
    have hm := Nat.mul_le_mul_left K hBA
    change 2≤K*I.B*(A+1)
    rw [Nat.mul_assoc]
    simp only [Nat.mul_one] at hm
    omega
  have hzeq : I.z=(⟨2,by change 2<A; omega⟩ : Fin A) := Fin.ext hz
  have hp' : cyclicFlag I.epos (numericColor (Nat.two_pow_pos _) (Nat.two_pow_pos _) I.hB E.orbit E.length
      (⟨2,by omega⟩ : Fin A)) (forward I.epos (I.first n) p)=true := by
    rw [I.flag_eq n] at hp
    change cyclicFlag I.epos (numericColor (Nat.two_pow_pos _) (Nat.two_pow_pos _) I.hB E.orbit E.length I.z)
      (forward I.epos (I.first n) p)=true at hp
    rw [hzeq] at hp
    exact hp
  have hq' : forward I.epos (I.first n) q=successor I.epos (forward I.epos (I.first n) p) ∨
      forward I.epos (I.first n) q=predecessor I.epos (forward I.epos (I.first n) p) := by
    rcases hq with hq|hq
    · exact Or.inl (by rw [hq,HamiltonNormalize.forward_successor])
    · exact Or.inr (by rw [hq,forward_predecessor])
  have hh := AACFoldFork.actual_buffered_neighbors (r:=I.r) (Nat.two_pow_pos _) hA4 I.hB h3
    (show 3≤I.B by have := I.hB4; omega) I.evenB E.orbit E.length I.epos hE2 E.injective G H
    (forward I.epos (I.first n) p) hp' (forward I.epos (I.first n) q) hq'
  constructor
  · rw [I.flag_eq n]
    change cyclicFlag I.epos (numericColor (Nat.two_pow_pos _) (Nat.two_pow_pos _) I.hB E.orbit E.length I.z)
      (forward I.epos (I.first n) q)=false
    rw [hzeq]
    exact hh.1
  · intro v hv
    apply forward_injective I.epos (I.first n)
    apply hh.2
    exact hv

section Opening
variable {X : Type} {R : X→X→Prop} {χ : X→Bool} {jR : Nat} (hj : 0<jR)

/-- Actual buffered source AACs open into a normalized fork with EXACT
original local-host union, after the literal first-mark rotation. All
neighbor, ordinal, output-ownership and size facts are derived internally. -/
theorem buffered_pair (I : Input) (hr : 2≤I.r) (hz : I.z.val=2) (h2 : 2≤jR)
    (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=jR) n),
      ∀u v,P.unionRelation u v ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) u v := by
  have hword := SourceGlobalMarks.word_length I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd n
  change 4≤(I.marks.word n).length at hword
  have hcard : 3≤Profile.cardinality (I.flag n) := by rw [I.mark_card n]; omega
  let m := markIndex (I.flag n) (⟨1,by omega⟩ : Fin (Profile.cardinality (I.flag n)))
  have hm : I.flag n m=true := (markIndex_spec (I.flag n) _).1
  have hleft (p : Fin I.E) (hp : p.val+1=m.val) : p=predecessor I.epos m := by
    have hs : successor I.epos p=m := by
      apply Fin.ext
      change (p.val+1)%I.E=m.val
      rw [hp,Nat.mod_eq_of_lt m.isLt]
    have hh := congrArg (predecessor I.epos) hs
    simpa only [predecessor_successor] using hh
  have hright (p : Fin I.E) (hp : p.val=m.val+1) : p=successor I.epos m := by
    apply Fin.ext
    change p.val=(m.val+1)%I.E
    rw [←hp,Nat.mod_eq_of_lt p.isLt]
  have hlf (p : Fin I.E) (hp : p.val+1=m.val) : I.flag n p=false :=
    (buffered_neighbors I hr hz n m p hm (Or.inr (hleft p hp))).1
  have hrf (p : Fin I.E) (hp : p.val=m.val+1) : I.flag n p=false :=
    (buffered_neighbors I hr hz n m p hm (Or.inl (hright p hp))).1
  have huniq (p : Fin I.E) (hp : p.val+1=m.val ∨ p.val=m.val+1) :
      ∀v,I.base n v=I.base n p→v=p := by
    rcases hp with hp|hp
    · exact (buffered_neighbors I hr hz n m p hm (Or.inr (hleft p hp))).2
    · exact (buffered_neighbors I hr hz n m p hm (Or.inl (hright p hp))).2
  have hlength := (I.decomposition hj h2 cycles n).2.2.2.2
  have hlarge : 3≤I.length (jR:=jR) n := by
    rw [hlength]
    have hm := Nat.mul_le_mul h2 (show 4≤I.E+(I.marks.word n).length by omega)
    omega
  have hreturn := AACFoldEdgeLedger.forest_return (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)
  let x := (cycles (I.schedule.active n)).vertex (⟨0,hj⟩,false)
  obtain ⟨P,hP⟩ := AACFoldFork.buffered_fork I.epos h2 (I.base n) (I.color n)
    (I.cut_mark n) (I.mark_unique n) (I.collision n) (cycles (I.schedule.active n))
    (I.layers hj cycles n) (I.selectors hj cycles n) (I.qpos n) hreturn (I.edge_unique n)
    hcard hlf hrf huniq hlarge x
  refine ⟨P,?_⟩
  intro u v
  exact (hP u v).trans (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n)
    (I.layers hj cycles n) (I.Host n) (I.host_cover n) u v)

/-- Two genuine simple paths of the full local cycle length, with EXACT
local input-host cover and unique physical edge positions. -/
noncomputable def buffered_paths (I : Input) (hr : 2≤I.r) (hz : I.z.val=2) (h2 : 2≤jR)
    (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    GraphPathDecomposition (I.Y×X)
      (AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n) (I.layers hj cycles n))
      (I.length (jR:=jR) n) := by
  let P := Classical.choose (buffered_pair hj I hr hz h2 cycles n)
  have hP := Classical.choose_spec (buffered_pair hj I hr hz h2 cycles n)
  let D := P.decomposition
  exact {
    Index := D.Index
    indices := D.indices
    vertices := D.vertices
    simple := D.simple
    adjacent := fun p hp j=>(hP _ _).mp (D.adjacent p hp j)
    cover := fun u v hh=>D.cover u v ((hP u v).mpr hh)
    unique := D.unique
  }
end Opening

/-- The actual chronological color word determines interval ordinal parity.
This bridge applies to the literal first-mark rotated source, independently
of whether its coefficient has any fixed number of binary ones. -/
theorem interior_color_parity (I : Input) (n : I.Index)
    (o p : InteriorIndex (I.flag n))
    (hc : I.color n (interiorIndex (I.flag n) o)≠I.color n (interiorIndex (I.flag n) p)) :
    o.1.val%2≠p.1.val%2 := by
  let c : Nat→Bool := fun k=>I.color n ⟨k%I.E,Nat.mod_lt _ I.epos⟩
  have ho := interior_run_rank I.epos (I.color n) (I.cut_mark n) o
  have hp := interior_run_rank I.epos (I.color n) (I.cut_mark n) p
  have hh : c (interiorIndex (I.flag n) o).val≠c (interiorIndex (I.flag n) p).val := by
    simpa only [c,Nat.mod_eq_of_lt (interiorIndex (I.flag n) o).isLt,
      Nat.mod_eq_of_lt (interiorIndex (I.flag n) p).isLt,Fin.eta] using hc
  have hs := changeRank_parity hh
  change changeRank c (interiorIndex (I.flag n) o).val=o.1.val at ho
  change changeRank c (interiorIndex (I.flag n) p).val=p.1.val at hp
  rw [ho,hp] at hs
  exact hs

#print axioms interior_color_parity
#print axioms buffered_pair
#print axioms buffered_paths
#print axioms buffered_neighbors
end ErdePaths.SourceFork
