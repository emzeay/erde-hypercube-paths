import ErdePaths.NoncrossingWord

namespace ErdePaths.LayerTour
open SquareLift PairedLayers NoncrossingWord

variable {X Label : Type} {R : X → X → Prop} {χ : X → Bool} {r : Nat} {hr : 0<r}

/-- Each layer contributes a before/after-vertical pair of actual vertices. -/
def tour (C : CycleData X R χ r hr) (fs : List (X → X)) (color : Bool)
    (p : Fin r × Fin fs.length × Bool) : Fin fs.length × X :=
  let y := prefixApply fs p.2.1.val (C.vertex (p.1,color))
  (p.2.1,if p.2.2 then fs[p.2.1.val] y else y)

theorem prefix_side (C : CycleData X R χ r hr) (fs : List (X → X)) (hfs : ValidWord χ fs)
    (color : Bool) (t : Fin r) (j : Fin fs.length) :
    χ (prefixApply fs j.val (C.vertex (t,color)))=flipN j.val color := by
  rw [prefixApply,applyWord_side (valid_take (hfs) j.val),C.bipartition]
  rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt j.isLt)]

theorem tour_side (C : CycleData X R χ r hr) (fs : List (X → X)) (hfs : ValidWord χ fs)
    (color : Bool) (p : Fin r × Fin fs.length × Bool) :
    χ (tour C fs color p).2=
      if p.2.2 then !flipN p.2.1.val color else flipN p.2.1.val color := by
  rcases p with ⟨t,j,b⟩
  cases b
  · exact prefix_side C fs hfs color t j
  · change χ (fs[j.val] (prefixApply fs j.val (C.vertex (t,color))))=_
    rw [(hfs _ (List.getElem_mem j.isLt)).2,prefix_side C fs hfs color t j]
    rfl

/-- The complete uniform tour vertex map is injective, before any graph
packaging. Different layers and before/after states cannot collide. -/
theorem tour_injective (C : CycleData X R χ r hr) (fs : List (X → X)) (hfs : ValidWord χ fs) (color : Bool) :
    Function.Injective (tour C fs color) := by
  intro p q he
  rcases p with ⟨t,j,b⟩
  rcases q with ⟨z,k,c⟩
  have hj : j=k := congrArg Prod.fst he
  subst k
  have hx := congrArg Prod.snd he
  have hside := congrArg χ hx
  rw [tour_side C fs hfs color (t,j,b),tour_side C fs hfs color (z,j,c)] at hside
  change (if b then !flipN j.val color else flipN j.val color)=
    (if c then !flipN j.val color else flipN j.val color) at hside
  have hb : b=c := by
    cases b <;> cases c <;> try rfl
    · cases h : flipN j.val color <;> simp [h] at hside
    · cases h : flipN j.val color <;> simp [h] at hside
  subst c
  have hprefix : prefixApply fs j.val (C.vertex (t,color))=
      prefixApply fs j.val (C.vertex (z,color)) := by
    cases b
    · exact hx
    · have hh := congrArg (fs[j.val]) hx
      have hi := (hfs _ (List.getElem_mem j.isLt)).1
      simpa only [tour,↓reduceIte,hi] using hh
  have ht := applyWord_injective (valid_take (hfs) j.val) hprefix
  have tz : t=z := congrArg Prod.fst (vertex_injective C ht)
  subst z
  rfl

/-- The actual horizontal-coordinate seam, including the last layer and the
last active clock coordinate, follows from the checked return. -/
theorem tour_outer_seam (C : CycleData X R χ r hr)
    (fs : List (X → X)) (_hfs : ValidWord χ fs) (color : Bool)
    (hreturn : ∀ t, applyWord fs (C.vertex (t,color))=C.vertex (successor hr t,color)) (t : Fin r)
    (j : Fin fs.length) (hj : j.val+1=fs.length) :
    (tour C fs color (t,j,true)).2=C.vertex (successor hr t,color) := by
  change fs[j.val]
    (prefixApply fs j.val (C.vertex (t,color)))=_
  rw [←prefix_advance (r:=r),hj]
  simpa only [prefixApply,List.take_length] using hreturn t

/-- Interior horizontal steps preserve the actual X vertex exactly. -/
theorem tour_inner_seam (C : CycleData X R χ r hr)
    (fs : List (X → X)) (_hfs : ValidWord χ fs) (color : Bool) (t : Fin r)
    (j : Fin fs.length) (hj : j.val+1<fs.length) :
    (tour C fs color (t,j,true)).2=
      (tour C fs color (t,⟨j.val+1,hj⟩,false)).2 := by
  exact (prefix_advance (r:=r) j (C.vertex (t,color))).symm

/-- All actual layer vertices are covered; no cardinality or Hamiltonicity
assumption about the output map is used. -/
theorem tour_surjective (C : CycleData X R χ r hr)
    (fs : List (X → X)) (hfs : ValidWord χ fs) (color : Bool) : Function.Surjective (tour C fs color) := by
  rintro ⟨j,x⟩
  have hp := valid_take (hfs) j.val
  obtain ⟨y,hy⟩ := applyWord_surjective hp x
  have represent (z : X) (hz : χ z=color) : ∃ t : Fin r, C.vertex (t,color)=z := by
    have he := C.vertex_coordinate z
    rcases hc : C.coordinate z with ⟨t,b⟩
    rw [hc] at he
    have hb : b=color := (C.bipartition t b).symm.trans ((congrArg χ he).trans hz)
    subst b
    exact ⟨t,he⟩
  by_cases hc : χ y=color
  · obtain ⟨t,ht⟩ := represent y hc
    refine ⟨(t,j,false),?_⟩
    have hv : prefixApply fs j.val (C.vertex (t,color))=x := by
      rw [ht]
      exact hy
    exact Prod.ext (show j=j from rfl) hv
  · let f := fs[j.val]
    have hf := hfs f (List.getElem_mem j.isLt)
    obtain ⟨z,hz⟩ := applyWord_surjective hp (f x)
    have hlen : (fs.take j.val).length=j.val := by
      rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt j.isLt)]
    have hyχ := applyWord_side hp y
    have hzχ := applyWord_side hp z
    rw [hy,hlen] at hyχ
    rw [hz,hlen,hf.2] at hzχ
    have hzy : χ z= !χ y := by
      apply flipN_injective j.val
      rw [flipN_not,←hyχ]
      exact hzχ.symm
    have hzcolor : χ z=color := by
      rw [hzy]
      cases hyc : χ y <;> cases color <;> simp_all
    obtain ⟨t,ht⟩ := represent z hzcolor
    refine ⟨(t,j,true),?_⟩
    have hv : f (prefixApply fs j.val (C.vertex (t,color)))=x := by
      rw [ht]
      exact (congrArg f hz).trans (hf.1 x)
    exact Prod.ext (show j=j from rfl) hv


theorem forestWord_valid (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    ValidWord χ (cycleWordColor C cycles inside outside color) := by
  cases color
  · exact cycleWordZero_valid C cycles inside outside
  · exact cycleWordOne_valid C cycles inside outside

theorem forestWord_advance (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) (t : Fin r) :
    applyWord (cycleWordColor C cycles inside outside color) (C.vertex (t,color))=
      C.vertex (successor hr t,color) := by
  rw [cycleWordColor_function]
  exact returnColor_advance C [] color t

theorem forestWord_length (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    (cycleWordColor C cycles inside outside color).length=2*(inside.pairCount+outside.pairCount+1) := by
  cases color <;> exact activeWord_length _ _ _ inside outside

/-- Actual noncrossing-grammar tour; no return or transitivity assumption is
among its inputs. The return is derived from passive forest cancellation. -/
def forestTour (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :=
  tour C (cycleWordColor C cycles inside outside color) color

theorem forestTour_bijective (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    Function.Injective (forestTour C cycles inside outside color) ∧
    Function.Surjective (forestTour C cycles inside outside color) :=
  ⟨tour_injective C _ (forestWord_valid C cycles inside outside color) color,
   tour_surjective C _ (forestWord_valid C cycles inside outside color) color⟩

theorem forestTour_outer_seam (C : CycleData X R χ r hr)
    (cycles : Label → CycleData X R χ r hr) (inside outside : Forest Label) (color : Bool)
    (t : Fin r) (j : Fin (cycleWordColor C cycles inside outside color).length)
    (hj : j.val+1=(cycleWordColor C cycles inside outside color).length) :
    (forestTour C cycles inside outside color (t,j,true)).2=C.vertex (successor hr t,color) :=
  tour_outer_seam C _ (forestWord_valid C cycles inside outside color) color
    (forestWord_advance C cycles inside outside color) t j hj

/-- Explicit conversion between the two traversal flags. -/
def flagIndex (b : Bool) : Fin 2 := if b then ⟨1,by decide⟩ else ⟨0,by decide⟩
def flagBool (b : Fin 2) : Bool := b.val==1

theorem flagBool_index (b : Bool) : flagBool (flagIndex b)=b := by cases b <;> rfl

theorem flagIndex_bool (b : Fin 2) : flagIndex (flagBool b)=b := by
  have hb : b.val=0 ∨ b.val=1 := by have := b.isLt; omega
  rcases hb with hb | hb
  · have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
    subst b; rfl
  · have he : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext hb
    subst b; rfl

def flagCoordinates {q : Nat} (p : Fin r × Fin q × Fin 2) : Fin r × Fin q × Bool :=
  (p.1,p.2.1,flagBool p.2.2)

theorem flagCoordinates_injective {q : Nat} : Function.Injective (@flagCoordinates r q) := by
  intro p z he
  have ht := congrArg Prod.fst he
  have hj := congrArg (fun x => x.2.1) he
  have hb := congrArg (fun x => flagIndex x.2.2) he
  simp only [flagCoordinates,flagIndex_bool] at ht hj hb
  exact Prod.ext ht (Prod.ext hj hb)

theorem flagCoordinates_surjective {q : Nat} : Function.Surjective (@flagCoordinates r q) := by
  rintro ⟨t,j,b⟩
  exact ⟨(t,j,flagIndex b),by simp only [flagCoordinates,flagBool_index]⟩

/-- Scalar cyclic clock with exactly one position per actual layered vertex. -/
def scalarTour (C : CycleData X R χ r hr) (fs : List (X → X)) (color : Bool)
    (hq : 0<fs.length) (i : Fin (r*(fs.length*2))) : Fin fs.length × X :=
  tour C fs color (flagCoordinates (Wiggle.indexCoordinates hq i))

theorem scalarTour_injective (C : CycleData X R χ r hr) (fs : List (X → X))
    (hfs : ValidWord χ fs) (color : Bool) (hq : 0<fs.length) :
    Function.Injective (scalarTour C fs color hq) := by
  intro i j he
  exact Wiggle.indexCoordinates_injective hq
    (flagCoordinates_injective (tour_injective C fs hfs color he))

theorem scalarTour_surjective (C : CycleData X R χ r hr) (fs : List (X → X))
    (hfs : ValidWord χ fs) (color : Bool) (hq : 0<fs.length) :
    Function.Surjective (scalarTour C fs color hq) := by
  intro x
  obtain ⟨p,hp⟩ := tour_surjective C fs hfs color x
  obtain ⟨z,hz⟩ := flagCoordinates_surjective p
  obtain ⟨i,hi⟩ := Wiggle.indexCoordinates_surjective hq z
  exact ⟨i,by simp only [scalarTour,hi,hz,hp]⟩

/-- Exact input matching edges plus cyclic horizontal edges. This is an actual
host relation, not a supplied output-cycle or ownership assertion. -/
def ScheduleAdjacent (fs : List (X → X)) (hq : 0<fs.length)
    (u v : Fin fs.length × X) : Prop :=
  (∃ (j : Fin fs.length) (x : X), SameEdge ((j,x),(j,(fs.get j) x)) (u,v)) ∨
  (∃ (j : Fin fs.length) (x : X), SameEdge ((j,x),(successor hq j,x)) (u,v))

theorem coordinateTour_step (C : CycleData X R χ r hr) (fs : List (X → X))
    (hfs : ValidWord χ fs) (color : Bool) (hq : 0<fs.length)
    (hreturn : ∀ t, applyWord fs (C.vertex (t,color))=C.vertex (successor hr t,color))
    (p : Fin r × Fin fs.length × Fin 2) :
    ScheduleAdjacent fs hq
      (tour C fs color (flagCoordinates p))
      (tour C fs color (flagCoordinates (Wiggle.coordinateNext hr hq p))) := by
  rcases p with ⟨t,j,b⟩
  by_cases hb : b.val=0
  · have he : b=(⟨0,by decide⟩ : Fin 2) := Fin.ext hb
    subst b
    refine Or.inl ⟨j,prefixApply fs j.val (C.vertex (t,color)),Or.inl ?_⟩
    rfl
  · have he : b=(⟨1,by decide⟩ : Fin 2) := Fin.ext (show b.val=1 from by have := b.isLt; omega)
    subst b
    by_cases hj : j.val+1<fs.length
    · have hs : successor hq j=(⟨j.val+1,hj⟩ : Fin fs.length) :=
        Fin.ext (Nat.mod_eq_of_lt hj)
      have hx := tour_inner_seam C fs hfs color t j hj
      refine Or.inr ⟨j,(tour C fs color (t,j,true)).2,Or.inl ?_⟩
      have hn : Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))=
          (t,⟨j.val+1,hj⟩,(⟨0,by decide⟩ : Fin 2)) := by simp [Wiggle.coordinateNext,hj]
      rw [hn]
      change ((j,(tour C fs color (t,j,true)).2),
        (successor hq j,(tour C fs color (t,j,true)).2))=
          (tour C fs color (t,j,true),tour C fs color (t,⟨j.val+1,hj⟩,false))
      rw [hs]
      exact Prod.ext rfl (Prod.ext rfl hx)
    · have hlast : j.val+1=fs.length := by have := j.isLt; omega
      have hs : successor hq j=(⟨0,hq⟩ : Fin fs.length) := by
        apply Fin.ext
        simp only [successor,hlast,Nat.mod_self]
      have hx := tour_outer_seam C fs hfs color hreturn t j hlast
      refine Or.inr ⟨j,C.vertex (successor hr t,color),Or.inl ?_⟩
      have hn : Wiggle.coordinateNext hr hq (t,j,(⟨1,by decide⟩ : Fin 2))=
          (successor hr t,⟨0,hq⟩,(⟨0,by decide⟩ : Fin 2)) := by simp [Wiggle.coordinateNext,hj]
      rw [hn]
      change ((j,C.vertex (successor hr t,color)),
        (successor hq j,C.vertex (successor hr t,color)))=
          (tour C fs color (t,j,true),tour C fs color (successor hr t,⟨0,hq⟩,false))
      rw [hs]
      exact Prod.ext (Prod.ext rfl hx.symm) rfl

theorem scalarTour_step (C : CycleData X R χ r hr) (fs : List (X → X))
    (hfs : ValidWord χ fs) (color : Bool) (hq : 0<fs.length)
    (hreturn : ∀ t, applyWord fs (C.vertex (t,color))=C.vertex (successor hr t,color))
    (i : Fin (r*(fs.length*2))) :
    ScheduleAdjacent fs hq (scalarTour C fs color hq i)
      (scalarTour C fs color hq (successor (Nat.mul_pos hr (by omega)) i)) := by
  simp only [scalarTour]
  rw [Wiggle.indexCoordinates_next hr hq i]
  exact coordinateTour_step C fs hfs color hq hreturn _

theorem forestWord_positive (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    0<(cycleWordColor C cycles inside outside color).length := by
  rw [forestWord_length]
  omega

/-- Each noncrossing-grammar schedule gives an actual Hamilton cyclic tour
in its input matching/horizontal host, with forced scalar cyclic successor. -/
theorem noncrossingHamiltonTour (C : CycleData X R χ r hr)
    (cycles : Label → CycleData X R χ r hr) (inside outside : Forest Label) (color : Bool) :
    let fs := cycleWordColor C cycles inside outside color
    let hq := forestWord_positive C cycles inside outside color
    Function.Injective (scalarTour C fs color hq) ∧
    Function.Surjective (scalarTour C fs color hq) ∧
    ∀ i, ScheduleAdjacent fs hq (scalarTour C fs color hq i)
      (scalarTour C fs color hq (successor (Nat.mul_pos hr (Nat.mul_pos hq (by decide))) i)) := by
  dsimp only
  have hv := forestWord_valid C cycles inside outside color
  refine ⟨scalarTour_injective C _ hv color _,scalarTour_surjective C _ hv color _,?_⟩
  exact scalarTour_step C _ hv color _ (forestWord_advance C cycles inside outside color)

#print axioms forestTour_bijective
#print axioms forestTour_outer_seam
#print axioms scalarTour_step
#print axioms scalarTour_surjective
#print axioms noncrossingHamiltonTour
end ErdePaths.LayerTour
