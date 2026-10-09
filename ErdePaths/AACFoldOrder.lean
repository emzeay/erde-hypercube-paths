import ErdePaths.AACIntervalSplit
import ErdePaths.AACUnfold

namespace ErdePaths.AACFoldOrder
open SquareLift AACIntervalSplit

/-- The right endpoint of an actual chronological gap. The final gap ends
at E, whose cyclic successor is the first mark at zero. -/
noncomputable def gapEnd {E : Nat} (S : Fin E → Bool)
    (j : Fin (Profile.cardinality S)) : Nat :=
  if h : j.val+1<Profile.cardinality S then
    (markIndex S ⟨j.val+1,h⟩).val else E

noncomputable def gapLength {E : Nat} (S : Fin E → Bool)
    (j : Fin (Profile.cardinality S)) : Nat :=
  gapEnd S j - (markIndex S j).val

theorem gapEnd_le {E : Nat} (S : Fin E → Bool) (j : Fin (Profile.cardinality S)) :
    gapEnd S j ≤ E := by
  unfold gapEnd
  split
  · have hh := (markIndex S ⟨j.val+1,by assumption⟩).isLt; omega
  · omega

theorem gapEnd_gt {E : Nat} (S : Fin E → Bool) (j : Fin (Profile.cardinality S)) :
    (markIndex S j).val < gapEnd S j := by
  unfold gapEnd
  split
  · exact markIndex_order S j _ (by simp <;> omega)
  · exact (markIndex S j).isLt

theorem gapLength_pos {E : Nat} (S : Fin E → Bool) (j : Fin (Profile.cardinality S)) :
    0<gapLength S j := by
  have hh := gapEnd_gt S j
  unfold gapLength
  omega

/-- Half-open chronological positions: offset zero is the actual mark and
positive offsets are the literal consecutive fine-clock interiors. -/
abbrev GapPosition {E : Nat} (S : Fin E → Bool) :=
  (j : Fin (Profile.cardinality S)) × Fin (gapLength S j)

noncomputable def gapIndex {E : Nat} (S : Fin E → Bool) (p : GapPosition S) : Fin E :=
  ⟨(markIndex S p.1).val+p.2.val,by
    have hh := p.2.isLt
    have he := gapEnd_le S p.1
    have hg := gapEnd_gt S p.1
    unfold gapLength at hh
    omega⟩

theorem gapIndex_bounds {E : Nat} (S : Fin E → Bool) (p : GapPosition S) :
    (markIndex S p.1).val ≤ (gapIndex S p).val ∧
    (gapIndex S p).val < gapEnd S p.1 := by
  have hh := p.2.isLt
  have hg := gapEnd_gt S p.1
  simp only [gapIndex]
  unfold gapLength at hh
  omega

theorem interior_iff_bounds {E : Nat} (S : Fin E → Bool)
    (j : Fin (Profile.cardinality S)) (n : Fin E) :
    n ∈ interiorPositions S j ↔
      (markIndex S j).val<n.val ∧ n.val<gapEnd S j := by
  rw [interior_gap_iff]
  constructor
  · rintro ⟨hl,hh⟩
    refine ⟨hl,?_⟩
    unfold gapEnd
    split
    · exact hh _ (by simp <;> omega)
    · exact n.isLt
  · rintro ⟨hl,hh⟩
    refine ⟨hl,?_⟩
    intro k hk
    have hj : j.val+1<Profile.cardinality S := by have := k.isLt; omega
    have hd : gapEnd S j=(markIndex S ⟨j.val+1,hj⟩).val := by simp [gapEnd,hj]
    rw [hd] at hh
    by_cases he : k.val=j.val+1
    · have hf : k=⟨j.val+1,hj⟩ := Fin.ext he
      simpa only [hf] using hh
    · have hm := markIndex_order S ⟨j.val+1,hj⟩ k (by simp <;> omega)
      omega

theorem gapIndex_zero {E : Nat} (S : Fin E → Bool) (j : Fin (Profile.cardinality S)) :
    gapIndex S ⟨j,⟨0,gapLength_pos S j⟩⟩=markIndex S j := by
  apply Fin.ext
  simp [gapIndex]

theorem gapIndex_interior {E : Nat} (S : Fin E → Bool) (p : GapPosition S)
    (hp : 0<p.2.val) : gapIndex S p ∈ interiorPositions S p.1 := by
  apply (interior_iff_bounds S p.1 _).mpr
  have hh := gapIndex_bounds S p
  exact ⟨by simp only [gapIndex]; omega,hh.2⟩

theorem gapIndex_injective {E : Nat} (S : Fin E → Bool) :
    Function.Injective (gapIndex S) := by
  intro p z he
  have hp := gapIndex_bounds S p
  have hz := gapIndex_bounds S z
  have hj : p.1=z.1 := by
    apply Fin.ext
    by_cases hlt : p.1.val<z.1.val
    · have hn : p.1.val+1<Profile.cardinality S := by have := z.1.isLt; omega
      have hd : gapEnd S p.1=(markIndex S ⟨p.1.val+1,hn⟩).val := by simp [gapEnd,hn]
      have hm : (markIndex S ⟨p.1.val+1,hn⟩).val ≤ (markIndex S z.1).val := by
        by_cases hh : p.1.val+1=z.1.val
        · have hf : (⟨p.1.val+1,hn⟩ : Fin (Profile.cardinality S))=z.1 := Fin.ext hh
          simp [hf]
        · have hm := markIndex_order S ⟨p.1.val+1,hn⟩ z.1 (by simp <;> omega)
          omega
      rw [hd,he] at hp
      omega
    · by_cases hgt : z.1.val<p.1.val
      · have hn : z.1.val+1<Profile.cardinality S := by have := p.1.isLt; omega
        have hd : gapEnd S z.1=(markIndex S ⟨z.1.val+1,hn⟩).val := by simp [gapEnd,hn]
        have hm : (markIndex S ⟨z.1.val+1,hn⟩).val ≤ (markIndex S p.1).val := by
          by_cases hh : z.1.val+1=p.1.val
          · have hf : (⟨z.1.val+1,hn⟩ : Fin (Profile.cardinality S))=p.1 := Fin.ext hh
            simp [hf]
          · have hm := markIndex_order S ⟨z.1.val+1,hn⟩ p.1 (by simp <;> omega)
            omega
        rw [hd,←he] at hz
        omega
      · omega
  rcases p with ⟨j,a⟩
  rcases z with ⟨k,b⟩
  change j=k at hj
  subst k
  have hab : a=b := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    simp only [gapIndex] at hv
    omega
  subst b
  rfl

theorem gapIndex_surjective {E : Nat} (hE : 0<E) (S : Fin E → Bool)
    (hzero : S ⟨0,hE⟩=true) : Function.Surjective (gapIndex S) := by
  intro n
  let j := runIndex hE S hzero n
  have hb : (markIndex S j).val≤n.val ∧ n.val<gapEnd S j := by
    cases hn : S n
    · have hi := (interior_iff_bounds S j n).mp (runIndex_interior hE S hzero n hn)
      omega
    · have hi := runIndex_mark hE S hzero n hn
      have hg := gapEnd_gt S j
      change markIndex S j=n at hi
      rw [hi] at hg
      exact ⟨by rw [hi]; omega,hg⟩
  refine ⟨⟨j,⟨n.val-(markIndex S j).val,?_⟩⟩,?_⟩
  · unfold gapLength
    omega
  · apply Fin.ext
    simp only [gapIndex]
    omega

/-- Each interior step is the actual fine-clock successor, not an assumed
edge of the unfolded output. -/
theorem gapIndex_step {E : Nat} (hE : 0<E) (S : Fin E → Bool)
    (p : GapPosition S) (hn : p.2.val+1<gapLength S p.1) :
    successor hE (gapIndex S p)=gapIndex S ⟨p.1,⟨p.2.val+1,hn⟩⟩ := by
  apply Fin.ext
  have hh := (gapIndex S ⟨p.1,⟨p.2.val+1,hn⟩⟩).isLt
  change ((markIndex S p.1).val+p.2.val+1)%E=
    (markIndex S p.1).val+(p.2.val+1)
  rw [Nat.mod_eq_of_lt (by simpa only [gapIndex,Nat.add_assoc] using hh)]
  omega

/-- The last outgoing fine edge lands at the next actual mark, including
last-gap wrap to the chosen cut. -/
theorem gapIndex_seam {E : Nat} (hE : 0<E) (S : Fin E → Bool)
    (hzero : S ⟨0,hE⟩=true) (hq : 0<Profile.cardinality S)
    (j : Fin (Profile.cardinality S)) :
    successor hE (gapIndex S ⟨j,⟨gapLength S j-1,by have := gapLength_pos S j; omega⟩⟩)=
      markIndex S (successor hq j) := by
  have hg := gapEnd_gt S j
  have hl := gapLength_pos S j
  have he : (markIndex S j).val+(gapLength S j-1)+1=gapEnd S j := by
    unfold gapLength at *
    omega
  by_cases hj : j.val+1<Profile.cardinality S
  · have hs : successor hq j=⟨j.val+1,hj⟩ := Fin.ext (Nat.mod_eq_of_lt hj)
    rw [hs]
    apply Fin.ext
    change ((markIndex S j).val+(gapLength S j-1)+1)%E=(markIndex S ⟨j.val+1,hj⟩).val
    rw [he]
    simp only [gapEnd,dite_eq_left hj,Nat.mod_eq_of_lt (markIndex S ⟨j.val+1,hj⟩).isLt]
  · have hjlast : j.val+1=Profile.cardinality S := by have := j.isLt; omega
    have hs : (successor hq j).val=0 := by simp [successor,hjlast]
    rw [markIndex_zero hE S hzero _ hs]
    apply Fin.ext
    change ((markIndex S j).val+(gapLength S j-1)+1)%E=0
    rw [he]
    simp [gapEnd,hj]

/-- Ragged expansion of the actual layered coordinate order. Arrival slots
have one outgoing J step; departure slots have exactly the chronological
number of fine AAC edges until the next mark. -/
noncomputable def foldWeight {E r : Nat} (S : Fin E → Bool)
    (p : Fin r × Fin (Profile.cardinality S) × Fin 2) : Nat :=
  if p.2.2.val=0 then 1 else gapLength S p.2.1

theorem foldWeight_pos {E r : Nat} (S : Fin E → Bool)
    (p : Fin r × Fin (Profile.cardinality S) × Fin 2) : 0<foldWeight S p := by
  unfold foldWeight
  split
  · omega
  · exact gapLength_pos S p.2.1

abbrev FoldPosition {E r : Nat} (S : Fin E → Bool) :=
  (p : Fin r × Fin (Profile.cardinality S) × Fin 2) × Fin (foldWeight S p)

noncomputable def foldNext {E r : Nat} (hr : 0<r) (S : Fin E → Bool)
    (hq : 0<Profile.cardinality S) (p : FoldPosition (r:=r) S) : FoldPosition (r:=r) S :=
  if h : p.2.val+1<foldWeight S p.1 then ⟨p.1,⟨p.2.val+1,h⟩⟩ else
    ⟨Wiggle.coordinateNext hr hq p.1,⟨0,foldWeight_pos S _⟩⟩

/-- The actual fine-clock coordinate of a ragged position. -/
noncomputable def foldBase {E r : Nat} (S : Fin E → Bool)
    (p : FoldPosition (r:=r) S) : Fin E :=
  if h : p.1.2.2.val=0 then markIndex S p.1.2.1 else
    gapIndex S ⟨p.1.2.1,⟨p.2.val,by
      have hh := p.2.isLt
      simpa only [foldWeight,dite_eq_right h,ite_false,h] using hh⟩⟩

/-- Every actual fine-clock occurrence is present in the departure expansion
at every turn index. No occurrence-surjectivity premise is supplied. -/
theorem foldBase_covers {E r : Nat} (hE : 0<E) (S : Fin E → Bool)
    (hzero : S ⟨0,hE⟩=true) (t : Fin r) (n : Fin E) :
    ∃p : FoldPosition (r:=r) S, p.1.1=t ∧ p.1.2.2.val=1 ∧ foldBase S p=n := by
  obtain ⟨⟨j,k⟩,hk⟩ := gapIndex_surjective hE S hzero n
  let p : FoldPosition (r:=r) S :=
    ⟨(t,j,⟨1,by decide⟩),⟨k.val,by simp [foldWeight]⟩⟩
  refine ⟨p,rfl,rfl,?_⟩
  simpa [p,foldBase] using hk

/-- Each expanded departure edge except the final one is literally the
fine Euler successor. -/
theorem foldBase_internal {E r : Nat} (hE : 0<E) (hr : 0<r)
    (S : Fin E → Bool) (hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) (hb : p.1.2.2.val≠0)
    (hn : p.2.val+1<foldWeight S p.1) :
    foldBase S (foldNext hr S hq p)=successor hE (foldBase S p) := by
  have hp : p.2.val<gapLength S p.1.2.1 := by
    simpa only [foldWeight,ite_false,hb] using p.2.isLt
  have hn' : p.2.val+1<gapLength S p.1.2.1 := by
    simpa only [foldWeight,ite_false,hb] using hn
  have hh := gapIndex_step hE S ⟨p.1.2.1,⟨p.2.val,hp⟩⟩ hn'
  rw [foldNext,dite_eq_left hn]
  simpa only [foldBase,dite_eq_right hb] using hh.symm

/-- At a departure boundary, both the actual base coordinate and layer
coordinate advance to the next chronological mark, including both seams. -/
theorem foldBase_boundary {E r : Nat} (hE : 0<E) (hr : 0<r)
    (S : Fin E → Bool) (hzero : S ⟨0,hE⟩=true)
    (hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) (hb : p.1.2.2.val≠0)
    (hn : ¬p.2.val+1<foldWeight S p.1) :
    foldBase S (foldNext hr S hq p)=successor hE (foldBase S p) := by
  rcases p with ⟨⟨t,j,b⟩,k⟩
  change b.val≠0 at hb
  have hv : b.val=1 := by have := b.isLt; omega
  have he : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hv
  subst b
  have hk : k.val=gapLength S j-1 := by
    have hh := k.isLt
    simp [foldWeight] at hh hn
    omega
  have hs := gapIndex_seam hE S hzero hq j
  have hj : (Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))).2.1=successor hq j := by
    by_cases hj : j.val+1<Profile.cardinality S
    · simp [Wiggle.coordinateNext,hj,successor,Nat.mod_eq_of_lt hj]
    · have he : j.val+1=Profile.cardinality S := by have := j.isLt; omega
      simp [Wiggle.coordinateNext,successor,he]
  have hflag : (Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))).2.2.val=0 := by
    simp [Wiggle.coordinateNext]
    split <;> rfl
  rw [foldNext,dite_eq_right hn]
  change foldBase S ⟨Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2)),_⟩=
    successor hE (foldBase S ⟨(t,j,(⟨1,by decide⟩ : Fin 2)),k⟩)
  simp only [foldBase,dite_eq_left hflag,hj,show ¬(1:Nat)=0 from by decide]
  have heq : (⟨k.val,by simpa [foldWeight] using k.isLt⟩ : Fin (gapLength S j))=
      ⟨gapLength S j-1,by have := gapLength_pos S j; omega⟩ := Fin.ext hk
  simp only [dite_false]
  rw [heq]
  exact hs.symm

/-- The J step leaves the base at the same literal mark. Its X endpoints
are supplied by `LayerPartition.commonTour_step`, never assumed as an
expanded output tour. -/
theorem foldBase_arrival {E r : Nat} (hr : 0<r) (S : Fin E → Bool)
    (hq : 0<Profile.cardinality S) (p : FoldPosition (r:=r) S)
    (hb : p.1.2.2.val=0) :
    foldBase S (foldNext hr S hq p)=foldBase S p := by
  rcases p with ⟨⟨t,j,b⟩,k⟩
  change b.val=0 at hb
  have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
  subst b
  have hk : k.val=0 := by have hh := k.isLt; simp [foldWeight] at hh; omega
  have hn : ¬k.val+1<foldWeight S (t,j,(⟨0,by decide⟩ : Fin 2)) := by simp [foldWeight,hk]
  rw [foldNext,dite_eq_right hn]
  simp only [Wiggle.coordinateNext]
  simp [foldBase,gapIndex]

#print axioms foldBase_arrival
#print axioms foldBase_covers
#print axioms foldBase_internal
#print axioms foldBase_boundary
#print axioms gapIndex_injective
#print axioms gapIndex_surjective
#print axioms gapIndex_step
#print axioms gapIndex_seam
end ErdePaths.AACFoldOrder
