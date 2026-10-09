import ErdePaths.AACFoldOrder

namespace ErdePaths.AACFoldGeometry
open SquareLift AACFoldOrder AACIntervalSplit PairedLayers LayerPartition LayerOwnership
variable {E r : Nat} {X : Type} {R : X→X→Prop} {χ : X→Bool} {hr : 0<r}

/-- The actual J-coordinate of every expanded position. A departure keeps
the same J vertex throughout its entire chronological base interval. -/
def foldJ (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (p : FoldPosition (r:=r) S) : X :=
  (commonTour C layers selectors color (LayerTour.flagCoordinates p.1)).2

theorem foldJ_internal (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (hq : 0<Profile.cardinality S) (p : FoldPosition (r:=r) S)
    (hn : p.2.val+1<foldWeight S p.1) :
    foldJ S C layers selectors color (foldNext hr S hq p)=foldJ S C layers selectors color p := by
  rw [foldNext,dite_eq_left hn]
  rfl

/-- At each base-interval boundary the actual J coordinate remains fixed,
including the final layer/turn seam. The checked return identity suffices. -/
theorem foldJ_boundary (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (hq : 0<Profile.cardinality S)
    (hreturn : ∀t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color))
    (p : FoldPosition (r:=r) S) (hb : p.1.2.2.val≠0)
    (hn : ¬p.2.val+1<foldWeight S p.1) :
    foldJ S C layers selectors color (foldNext hr S hq p)=foldJ S C layers selectors color p := by
  have hs := commonTour_step C layers selectors color hq hreturn p.1
  have ht := congrArg (fun e => e.2.2) hs
  have hu := congrArg (fun e => e.1.2) hs
  rw [foldNext,dite_eq_right hn]
  unfold foldJ
  rw [ht,hu]
  have hb1 : p.1.2.2.val=1 := by have := p.1.2.2.isLt; omega
  simp [outputEdge,LayerTour.flagBool,hb1]

/-- Every arrival edge is an actual matching edge of its assigned J cycle;
there is no output-adjacency input. -/
theorem foldJ_arrival (S : Fin E→Bool) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (hR : ∀u v, R u v→R v u) (hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) (hb : p.1.2.2.val=0) :
    R (foldJ S C layers selectors color p)
      (foldJ S C layers selectors color (foldNext hr S hq p)) := by
  have hn : ¬p.2.val+1<foldWeight S p.1 := by
    simp only [foldWeight,hb,ite_true]
    omega
  rw [foldNext,dite_eq_right hn]
  rcases p with ⟨⟨t,j,b⟩,k⟩
  change b.val=0 at hb
  have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
  subst b
  change R (arrival C layers selectors color j t) (departure C layers selectors color j t)
  unfold departure choose
  cases selectors j ^^ color
  · exact matchingA_adjacent (layers j) hR _
  · exact matchingB_adjacent (layers j) hR _

variable {Y : Type}

noncomputable def foldVertex (S : Fin E→Bool) (base : Fin E→Y) (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (p : FoldPosition (r:=r) S) : Y×X :=
  (base (foldBase S p),foldJ S C layers selectors color p)

/-- Actual Cartesian adjacency of the expanded chronological walk. Only
the base Euler edges and the proved layer return are inputs. -/
theorem foldVertex_step {Q : Y→Y→Prop} (hE : 0<E) (S : Fin E→Bool)
    (hzero : S ⟨0,hE⟩=true) (base : Fin E→Y)
    (hbase : ∀n, Q (base n) (base (successor hE n)))
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality S)→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality S)→Bool) (color : Bool)
    (hR : ∀u v, R u v→R v u) (hq : 0<Profile.cardinality S)
    (hreturn : ∀t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) (p : FoldPosition (r:=r) S) :
    AnchoredEmbedding.ProductRelation Q R (foldVertex S base C layers selectors color p)
      (foldVertex S base C layers selectors color (foldNext hr S hq p)) := by
  by_cases hb : p.1.2.2.val=0
  · exact Or.inr ⟨congrArg base (foldBase_arrival hr S hq p hb).symm,
      foldJ_arrival S C layers selectors color hR hq p hb⟩
  · by_cases hn : p.2.val+1<foldWeight S p.1
    · exact Or.inl ⟨(foldJ_internal S C layers selectors color hq p hn).symm,by
        change Q (base (foldBase S p)) (base (foldBase S (foldNext hr S hq p)))
        rw [foldBase_internal hE hr S hq p hb hn]
        exact hbase _⟩
    · exact Or.inl ⟨(foldJ_boundary S C layers selectors color hq hreturn p hb hn).symm,by
        change Q (base (foldBase S p)) (base (foldBase S (foldNext hr S hq p)))
        rw [foldBase_boundary hE hr S hzero hq p hb hn]
        exact hbase _⟩

/-- Every positive gap offset has a literal occurrence in the existing
chronological interior list; its index is constructed from list membership. -/
noncomputable def gapOccurrence (S : Fin E→Bool) (p : GapPosition S) (hp : 0<p.2.val) :
    InteriorIndex S :=
  ⟨p.1,⟨Classical.choose (List.mem_iff_getElem.mp (gapIndex_interior S p hp)),
    (Classical.choose_spec (List.mem_iff_getElem.mp (gapIndex_interior S p hp))).1⟩⟩

theorem gapOccurrence_index (S : Fin E→Bool) (p : GapPosition S) (hp : 0<p.2.val) :
    interiorIndex S (gapOccurrence S p hp)=gapIndex S p := by
  exact (Classical.choose_spec (List.mem_iff_getElem.mp (gapIndex_interior S p hp))).2

theorem gapOccurrence_injective (S : Fin E→Bool) (p z : GapPosition S)
    (hp : 0<p.2.val) (hz : 0<z.2.val) (he : gapOccurrence S p hp=gapOccurrence S z hz) : p=z := by
  apply gapIndex_injective S
  have hi := congrArg (interiorIndex S) he
  simpa only [gapOccurrence_index] using hi

/-- The literal contracted-mark / chronological-interior position carrier.
For S=cyclicFlag this is exactly AACUnfold.Position of AACIntervalSplit.split. -/
abbrev Position (S : Fin E→Bool) (r : Nat) :=
  (Fin r × Fin (Profile.cardinality S) × Bool) ⊕ (InteriorIndex S × Fin r)

noncomputable def position (S : Fin E→Bool) (p : FoldPosition (r:=r) S) : Position S r :=
  if hb : p.1.2.2.val=0 then .inl (p.1.1,p.1.2.1,false)
  else if hk : p.2.val=0 then .inl (p.1.1,p.1.2.1,true)
  else .inr (gapOccurrence S ⟨p.1.2.1,⟨p.2.val,by
    simpa only [foldWeight,ite_false,hb] using p.2.isLt⟩⟩ (by change 0<p.2.val; omega),p.1.1)

theorem foldPosition_ext (S : Fin E→Bool) (p z : FoldPosition (r:=r) S)
    (ht : p.1.1=z.1.1) (hj : p.1.2.1=z.1.2.1)
    (hb : p.1.2.2.val=z.1.2.2.val) (hk : p.2.val=z.2.val) : p=z := by
  rcases p with ⟨a,k⟩
  rcases z with ⟨b,l⟩
  have hab : a=b := Prod.ext ht (Prod.ext hj (Fin.ext hb))
  subst b
  have hkl : k=l := Fin.ext hk
  subst l
  rfl

theorem position_injective (S : Fin E→Bool) : Function.Injective (position (r:=r) S) := by
  intro p z he
  by_cases hp : p.1.2.2.val=0
  · by_cases hz : z.1.2.2.val=0
    · simp only [position,dite_eq_left hp,dite_eq_left hz,Sum.inl.injEq,Prod.mk.injEq] at he
      have hk : p.2.val=0 := by have hh := p.2.isLt; simp only [foldWeight,hp,ite_true] at hh; omega
      have hl : z.2.val=0 := by have hh := z.2.isLt; simp only [foldWeight,hz,ite_true] at hh; omega
      exact foldPosition_ext S p z he.1 he.2.1 (by omega) (by omega)
    · by_cases hk : z.2.val=0
      · simp [position,hp,hz,hk] at he
      · simp [position,hp,hz,hk] at he
  · by_cases hz : z.1.2.2.val=0
    · by_cases hk : p.2.val=0
      · simp [position,hp,hz,hk] at he
      · simp [position,hp,hz,hk] at he
    · have hb : p.1.2.2.val=z.1.2.2.val := by
        have hh := p.1.2.2.isLt
        have hi := z.1.2.2.isLt
        omega
      by_cases hk : p.2.val=0
      · by_cases hl : z.2.val=0
        · simp only [position,dite_eq_right hp,dite_eq_right hz,dite_eq_left hk,dite_eq_left hl,
            Sum.inl.injEq,Prod.mk.injEq] at he
          exact foldPosition_ext S p z he.1 he.2.1 hb (by omega)
        · simp [position,hp,hz,hk,hl] at he
      · by_cases hl : z.2.val=0
        · simp [position,hp,hz,hk,hl] at he
        · simp only [position,dite_eq_right hp,dite_eq_right hz,dite_eq_right hk,dite_eq_right hl,
            Sum.inr.injEq,Prod.mk.injEq] at he
          have hg := gapOccurrence_injective S _ _ _ _ he.1
          have hj := congrArg Sigma.fst hg
          have hval := congrArg (fun o => o.2.val) hg
          exact foldPosition_ext S p z he.2 hj hb hval

theorem position_surjective (S : Fin E→Bool) : Function.Surjective (position (r:=r) S) := by
  intro z
  cases z with
  | inl z =>
    rcases z with ⟨t,j,b⟩
    cases b
    · let p : FoldPosition (r:=r) S := ⟨(t,j,⟨0,by decide⟩),⟨0,by simp [foldWeight]⟩⟩
      exact ⟨p,by simp [position,p]⟩
    · let p : FoldPosition (r:=r) S := ⟨(t,j,⟨1,by decide⟩),⟨0,by
        simpa only [foldWeight,show ¬(1:Nat)=0 by decide,ite_false] using gapLength_pos S j⟩⟩
      exact ⟨p,by simp [position,p]⟩
  | inr z =>
    rcases z with ⟨o,t⟩
    have hmem : interiorIndex S o∈interiorPositions S o.1 := List.getElem_mem o.2.isLt
    have hb := (interior_iff_bounds S o.1 (interiorIndex S o)).mp hmem
    let k := (interiorIndex S o).val-(markIndex S o.1).val
    have hk : 0<k := by dsimp only [k]; omega
    have hlt : k<gapLength S o.1 := by unfold gapLength; dsimp only [k]; omega
    let g : GapPosition S := ⟨o.1,⟨k,hlt⟩⟩
    have hg : gapIndex S g=interiorIndex S o := by
      apply Fin.ext
      change (markIndex S o.1).val+k=(interiorIndex S o).val
      dsimp only [k]
      omega
    let p : FoldPosition (r:=r) S := ⟨(t,o.1,⟨1,by decide⟩),⟨k,by
      simpa only [foldWeight,show ¬(1:Nat)=0 by decide,ite_false] using hlt⟩⟩
    have hc : gapOccurrence S g hk=o :=
      interiorIndex_injective S ((gapOccurrence_index S g hk).trans hg)
    refine ⟨p,?_⟩
    change position S p=Sum.inr (o,t)
    simp only [position,p,show ¬(1:Nat)=0 by decide,dite_false,show k≠0 by omega]
    rw [hc]

/-- Literal bijection to the exact unfolded mark/interior carrier. It has
no input output-coverage or output-injectivity hypothesis. -/
theorem position_bijective (S : Fin E→Bool) :
    Function.Injective (position (r:=r) S) ∧ Function.Surjective (position (r:=r) S) :=
  ⟨position_injective S,position_surjective S⟩

/-- The coordinate bijection lands in the actual split's unfolded carrier,
and evaluates to the same literal physical base/J vertex. -/
theorem unfold_vertex_position (hE : 0<E) (base : Fin E→Y) (baseColor : Fin E→Bool)
    (hcut : AACMarkIntervals.cyclicFlag hE baseColor ⟨0,hE⟩=true)
    (hmark : ∀n m, AACMarkIntervals.cyclicFlag hE baseColor n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→Bool) (color : Bool)
    (p : FoldPosition (r:=r) (AACMarkIntervals.cyclicFlag hE baseColor)) :
    AACUnfold.vertex (split hE base baseColor hcut hmark hcollision) C layers selectors color
      (position (AACMarkIntervals.cyclicFlag hE baseColor) p)=
      foldVertex (AACMarkIntervals.cyclicFlag hE baseColor) base C layers selectors color p := by
  rcases p with ⟨⟨t,j,b⟩,k⟩
  by_cases hb : b.val=0
  · have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
    subst b
    rfl
  · have he : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext (by change b.val=1; have := b.isLt; omega)
    subst b
    by_cases hk : k.val=0
    · apply Prod.ext
      · simp only [position,show ¬(1:Nat)=0 by decide,dite_false,hk,dite_true,
          AACUnfold.vertex,split,foldVertex,foldBase]
        rw [gapIndex_zero]

      · simp [position,hk,AACUnfold.vertex,foldVertex,foldJ,LayerTour.flagCoordinates,LayerTour.flagBool,commonTour]
    · apply Prod.ext
      · simp only [position,show ¬(1:Nat)=0 by decide,dite_false,hk,
          AACUnfold.vertex,split,foldVertex,foldBase]
        rw [gapOccurrence_index]
      · simp [position,hk,AACUnfold.vertex,foldVertex,foldJ,LayerTour.flagCoordinates,LayerTour.flagBool,commonTour,gapOccurrence]

/-- Actual folded physical simplicity follows from the base mark/collision
laws and the newly constructed coordinate bijection, not an output oracle. -/
theorem foldVertex_injective (hE : 0<E) (base : Fin E→Y) (baseColor : Fin E→Bool)
    (hcut : AACMarkIntervals.cyclicFlag hE baseColor ⟨0,hE⟩=true)
    (hmark : ∀n m, AACMarkIntervals.cyclicFlag hE baseColor n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→Bool) (color : Bool) :
    Function.Injective (foldVertex (AACMarkIntervals.cyclicFlag hE baseColor) base C layers selectors color) := by
  intro p z he
  apply position_injective (AACMarkIntervals.cyclicFlag hE baseColor)
  apply AACUnfold.vertex_injective (split hE base baseColor hcut hmark hcollision) C layers selectors color
  rw [unfold_vertex_position,unfold_vertex_position]
  exact he

#print axioms foldVertex_injective
#print axioms unfold_vertex_position

#print axioms position_bijective

#print axioms foldVertex_step
#print axioms gapOccurrence_index
#print axioms foldJ_boundary
#print axioms foldJ_arrival
end ErdePaths.AACFoldGeometry
