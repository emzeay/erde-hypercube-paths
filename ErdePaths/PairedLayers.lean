import ErdePaths.AnchoredAssembly

namespace ErdePaths.PairedLayers
open SquareLift

/-- Explicit inverse of the cyclic successor; all dimensions are uniform. -/
def previous {r : Nat} (hr : 0<r) (t : Fin r) : Fin r :=
  if h : t.val=0 then ⟨r-1,by omega⟩ else ⟨t.val-1,by omega⟩

theorem next_previous {r : Nat} (hr : 0<r) (t : Fin r) : successor hr (previous hr t)=t := by
  apply Fin.ext
  simp only [previous]
  split
  · simp only [successor]
    have hsum : r-1+1=r := by omega
    rw [hsum,Nat.mod_self]
    omega
  · simp only [successor]
    have hsum : t.val-1+1=t.val := by omega
    rw [hsum,Nat.mod_eq_of_lt t.isLt]

theorem previous_next {r : Nat} (hr : 0<r) (t : Fin r) : previous hr (successor hr t)=t := by
  apply Fin.ext
  by_cases h : t.val+1<r
  · have hn : (successor hr t).val=t.val+1 := Nat.mod_eq_of_lt h
    simp [previous,hn] <;> omega
  · have hn : (successor hr t).val=0 := by
      have ht : t.val+1=r := by omega
      simp only [successor,ht,Nat.mod_self]
    simp [previous,hn] <;> omega

/-- An actual bipartite Hamilton clock, with explicit inverse. The two edge
formulas list all consecutive cycle edges; no matching or return is assumed. -/
structure CycleData (X : Type) (R : X → X → Prop) (χ : X → Bool)
    (r : Nat) (hr : 0<r) where
  vertex : Fin r × Bool → X
  coordinate : X → Fin r × Bool
  coordinate_vertex : ∀ p, coordinate (vertex p)=p
  vertex_coordinate : ∀ x, vertex (coordinate x)=x
  bipartition : ∀ t b, χ (vertex (t,b))=b
  edge_even : ∀ t, R (vertex (t,false)) (vertex (t,true))
  edge_odd : ∀ t, R (vertex (t,true)) (vertex (successor hr t,false))

variable {X : Type} {R : X → X → Prop} {χ : X → Bool} {r : Nat} {hr : 0<r}

def swapA (p : Fin r × Bool) : Fin r × Bool := (p.1,!p.2)
def swapB (hr : 0<r) (p : Fin r × Bool) : Fin r × Bool :=
  if p.2 then (successor hr p.1,false) else (previous hr p.1,true)

def matchingA (C : CycleData X R χ r hr) (x : X) := C.vertex (swapA (C.coordinate x))
def matchingB (C : CycleData X R χ r hr) (x : X) := C.vertex (swapB hr (C.coordinate x))

theorem matchingA_vertex (C : CycleData X R χ r hr) (t : Fin r) (b : Bool) :
    matchingA C (C.vertex (t,b))=C.vertex (t,!b) := by
  simp only [matchingA,C.coordinate_vertex,swapA]

theorem matchingB_even (C : CycleData X R χ r hr) (t : Fin r) :
    matchingB C (C.vertex (t,false))=C.vertex (previous hr t,true) := by
  simp only [matchingB,C.coordinate_vertex,swapB,Bool.false_eq_true,↓reduceIte]

theorem matchingB_odd (C : CycleData X R χ r hr) (t : Fin r) :
    matchingB C (C.vertex (t,true))=C.vertex (successor hr t,false) := by
  simp only [matchingB,C.coordinate_vertex,swapB,↓reduceIte]

theorem matchingA_involutive (C : CycleData X R χ r hr) (x : X) : matchingA C (matchingA C x)=x := by
  rw [←C.vertex_coordinate x]
  rcases C.coordinate x with ⟨t,b⟩
  rw [matchingA_vertex,matchingA_vertex]
  cases b <;> rfl

theorem matchingB_involutive (C : CycleData X R χ r hr) (x : X) : matchingB C (matchingB C x)=x := by
  have hx := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,b⟩
  rw [hc] at hx
  rw [←hx]
  cases b
  · rw [matchingB_even,matchingB_odd,next_previous]
  · rw [matchingB_odd,matchingB_even,previous_next]

/-- Actual matching edges belong to the input Hamilton cycle relation. -/
theorem matchingA_adjacent (C : CycleData X R χ r hr)
    (hR : ∀ x y, R x y → R y x) (x : X) : R x (matchingA C x) := by
  have hx := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,b⟩
  rw [hc] at hx
  rw [←hx,matchingA_vertex]
  cases b
  · exact C.edge_even t
  · exact hR _ _ (C.edge_even t)

theorem matchingB_adjacent (C : CycleData X R χ r hr)
    (hR : ∀ x y, R x y → R y x) (x : X) : R x (matchingB C x) := by
  have hx := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,b⟩
  rw [hc] at hx
  rw [←hx]
  cases b
  · rw [matchingB_even]
    have he := C.edge_odd (previous hr t)
    rw [next_previous] at he
    exact hR _ _ he
  · rw [matchingB_odd]
    exact C.edge_odd t

/-- Apply an ordered word of vertex permutations, earliest letter first. -/
def applyWord : List (X → X) → X → X
  | [],x => x
  | f::fs,x => applyWord fs (f x)

/-- A passive pair contributes literally the identity, without commutation. -/
theorem passivePair_cancel (f : X → X) (hf : ∀ x, f (f x)=x)
    (fs : List (X → X)) (x : X) : applyWord (f::f::fs) x=applyWord fs x := by
  simp only [applyWord,hf]

def passiveWordA : List (CycleData X R χ r hr) → List (X → X)
  | [] => []
  | C::Cs => matchingA C::matchingA C::passiveWordA Cs

def passiveWordB : List (CycleData X R χ r hr) → List (X → X)
  | [] => []
  | C::Cs => matchingB C::matchingB C::passiveWordB Cs

theorem passiveWordA_identity (Cs : List (CycleData X R χ r hr)) (x : X) :
    applyWord (passiveWordA Cs) x=x := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
    simp only [passiveWordA,passivePair_cancel _ (matchingA_involutive C),ih]

theorem passiveWordB_identity (Cs : List (CycleData X R χ r hr)) (x : X) :
    applyWord (passiveWordB Cs) x=x := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
    simp only [passiveWordB,passivePair_cancel _ (matchingB_involutive C),ih]

def returnZero (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) : X → X :=
  applyWord (matchingA C::matchingB C::passiveWordA Cs)
def returnOne (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) : X → X :=
  applyWord (matchingB C::matchingA C::passiveWordB Cs)

theorem returnZero_formula (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (x : X) :
    returnZero C Cs x=matchingB C (matchingA C x) := by
  simp only [returnZero,applyWord,passiveWordA_identity]

theorem returnOne_formula (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (x : X) :
    returnOne C Cs x=matchingA C (matchingB C x) := by
  simp only [returnOne,applyWord,passiveWordB_identity]

/-- Monodromy is derived from the actual active Hamilton clock. -/
theorem returnZero_advance (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (t : Fin r) :
    returnZero C Cs (C.vertex (t,false))=C.vertex (successor hr t,false) := by
  rw [returnZero_formula,matchingA_vertex]
  exact matchingB_odd C t

theorem returnOne_advance (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (t : Fin r) :
    returnOne C Cs (C.vertex (t,true))=C.vertex (successor hr t,true) := by
  rw [returnOne_formula,matchingB_odd,matchingA_vertex]
  rfl

def returnColor (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (b : Bool) : X → X :=
  if b then returnOne C Cs else returnZero C Cs

theorem returnColor_advance (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr))
    (b : Bool) (t : Fin r) : returnColor C Cs b (C.vertex (t,b))=C.vertex (successor hr t,b) := by
  cases b
  · exact returnZero_advance C Cs t
  · exact returnOne_advance C Cs t

def power (f : X → X) : Nat → X → X
  | 0,x => x
  | n+1,x => f (power f n x)

/-- Every position is reached by the return, derived solely from the active
Hamilton vertex clock, regardless of all passive cyclic orders. -/
theorem returnColor_power (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr))
    (b : Bool) (t : Fin r) :
    power (returnColor C Cs b) t.val (C.vertex (⟨0,hr⟩,b))=C.vertex (t,b) := by
  have aux : ∀ n (hn : n<r),
      power (returnColor C Cs b) n (C.vertex (⟨0,hr⟩,b))=C.vertex (⟨n,hn⟩,b) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      rw [power,ih (by omega),returnColor_advance]
      apply congrArg C.vertex
      apply Prod.ext
      · apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      · rfl
  exact aux t.val t.isLt

theorem vertex_injective (C : CycleData X R χ r hr) : Function.Injective C.vertex := by
  intro p q hpq
  have he := congrArg C.coordinate hpq
  simpa only [C.coordinate_vertex] using he

/-- No two return positions before the first full circuit coincide. -/
theorem returnColor_orbit_injective (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (b : Bool) :
    Function.Injective (fun t : Fin r =>
      power (returnColor C Cs b) t.val (C.vertex (⟨0,hr⟩,b))) := by
  intro t z he
  simp only [returnColor_power] at he
  exact congrArg Prod.fst (vertex_injective C he)

/-- The return orbit covers the entire corresponding common bipartition.
Transitivity is a conclusion, not an independently assumed monodromy fact. -/
theorem returnColor_orbit_covers (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (b : Bool) (x : X) (hx : χ x=b) :
    ∃ t : Fin r, power (returnColor C Cs b) t.val (C.vertex (⟨0,hr⟩,b))=x := by
  have he := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,c⟩
  rw [hc] at he
  have hb : c=b := by
    calc
      c = χ (C.vertex (t,c)) := (C.bipartition t c).symm
      _ = χ x := congrArg χ he
      _ = b := hx
  subst c
  exact ⟨t,(returnColor_power C Cs b t).trans he⟩

theorem returnColor_orbit_closes (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (b : Bool) :
    power (returnColor C Cs b) r (C.vertex (⟨0,hr⟩,b))=C.vertex (⟨0,hr⟩,b) := by
  have hlast := returnColor_power C Cs b (⟨r-1,by omega⟩ : Fin r)
  have hsum : r=r-1+1 := by omega
  have hrew := congrArg (fun n => power (returnColor C Cs b) n (C.vertex (⟨0,hr⟩,b))) hsum
  apply hrew.trans
  change returnColor C Cs b (power (returnColor C Cs b) (r-1) (C.vertex (⟨0,hr⟩,b)))=_
  rw [hlast,returnColor_advance]
  apply congrArg C.vertex
  apply Prod.ext
  · apply Fin.ext
    simp only [successor]
    have hsum' : r-1+1=r := by omega
    rw [hsum',Nat.mod_self]
  · rfl

theorem matchingA_flips (C : CycleData X R χ r hr) (x : X) : χ (matchingA C x)= !χ x := by
  have he := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,b⟩
  rw [hc] at he
  rw [←he,matchingA_vertex,C.bipartition,C.bipartition]

theorem matchingB_flips (C : CycleData X R χ r hr) (x : X) : χ (matchingB C x)= !χ x := by
  have he := C.vertex_coordinate x
  rcases hc : C.coordinate x with ⟨t,b⟩
  rw [hc] at he
  rw [←he]
  cases b
  · rw [matchingB_even,C.bipartition,C.bipartition]
    rfl
  · rw [matchingB_odd,C.bipartition,C.bipartition]
    rfl

/-- The actual layer matching schedules, with the active pair first. -/
def schedule (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (b : Bool) : List (X → X) :=
  if b then matchingB C::matchingA C::passiveWordB Cs
  else matchingA C::matchingB C::passiveWordA Cs

def ValidWord (χ : X → Bool) (fs : List (X → X)) : Prop :=
  ∀ f, f ∈ fs → (∀ x, f (f x)=x) ∧ (∀ x, χ (f x)= !χ x)

theorem passiveWordA_valid (Cs : List (CycleData X R χ r hr)) : ValidWord χ (passiveWordA Cs) := by
  induction Cs with
  | nil => intro f hf; cases hf
  | cons C Cs ih =>
    intro f hf
    simp only [passiveWordA,List.mem_cons] at hf
    rcases hf with h | h | h
    · subst f; exact ⟨matchingA_involutive C,matchingA_flips C⟩
    · subst f; exact ⟨matchingA_involutive C,matchingA_flips C⟩
    · exact ih f h

theorem passiveWordB_valid (Cs : List (CycleData X R χ r hr)) : ValidWord χ (passiveWordB Cs) := by
  induction Cs with
  | nil => intro f hf; cases hf
  | cons C Cs ih =>
    intro f hf
    simp only [passiveWordB,List.mem_cons] at hf
    rcases hf with h | h | h
    · subst f; exact ⟨matchingB_involutive C,matchingB_flips C⟩
    · subst f; exact ⟨matchingB_involutive C,matchingB_flips C⟩
    · exact ih f h

theorem schedule_valid (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (b : Bool) :
    ValidWord χ (schedule C Cs b) := by
  cases b <;> intro f hf <;> simp only [schedule,Bool.false_eq_true,↓reduceIte,List.mem_cons] at hf
  · rcases hf with h | h | h
    · subst f; exact ⟨matchingA_involutive C,matchingA_flips C⟩
    · subst f; exact ⟨matchingB_involutive C,matchingB_flips C⟩
    · exact passiveWordA_valid Cs f h
  · rcases hf with h | h | h
    · subst f; exact ⟨matchingB_involutive C,matchingB_flips C⟩
    · subst f; exact ⟨matchingA_involutive C,matchingA_flips C⟩
    · exact passiveWordB_valid Cs f h

theorem schedule_return (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (b : Bool) (x : X) :
    applyWord (schedule C Cs b) x=returnColor C Cs b x := by
  cases b <;> rfl

theorem valid_take {fs : List (X → X)} (h : ValidWord χ fs) (n : Nat) : ValidWord χ (fs.take n) := by
  intro f hf
  exact h f (List.mem_of_mem_take hf)

theorem applyWord_injective {fs : List (X → X)} (h : ValidWord χ fs) : Function.Injective (applyWord fs) := by
  induction fs with
  | nil => intro x y he; exact he
  | cons f fs ih =>
    have hf := (h f (List.mem_cons_self)).1
    have ht : ValidWord χ fs := fun g hg => h g (List.mem_cons_of_mem f hg)
    intro x y he
    have he' := congrArg f (ih ht he)
    simpa only [hf] using he'

def flipN : Nat → Bool → Bool
  | 0,b => b
  | n+1,b => flipN n (!b)

theorem applyWord_side {fs : List (X → X)} (h : ValidWord χ fs) (x : X) :
    χ (applyWord fs x)=flipN fs.length (χ x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    have ht : ValidWord χ fs := fun g hg => h g (List.mem_cons_of_mem f hg)
    rw [applyWord,ih ht, (h f List.mem_cons_self).2 x]
    rfl

def prefixApply (fs : List (X → X)) (j : Nat) (x : X) : X := applyWord (fs.take j) x

/-- Each layer contributes a before/after-vertical pair of actual vertices. -/
def layerTour (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (color : Bool)
    (p : Fin r × Fin (schedule C Cs color).length × Bool) : Fin (schedule C Cs color).length × X :=
  let y := prefixApply (schedule C Cs color) p.2.1.val (C.vertex (p.1,color))
  (p.2.1,if p.2.2 then (schedule C Cs color)[p.2.1.val] y else y)

theorem prefix_side (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr))
    (color : Bool) (t : Fin r) (j : Fin (schedule C Cs color).length) :
    χ (prefixApply (schedule C Cs color) j.val (C.vertex (t,color)))=flipN j.val color := by
  rw [prefixApply,applyWord_side (valid_take (schedule_valid C Cs color) j.val),C.bipartition]
  rw [List.length_take,Nat.min_eq_left (Nat.le_of_lt j.isLt)]

theorem layerTour_side (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr))
    (color : Bool) (p : Fin r × Fin (schedule C Cs color).length × Bool) :
    χ (layerTour C Cs color p).2=
      if p.2.2 then !flipN p.2.1.val color else flipN p.2.1.val color := by
  rcases p with ⟨t,j,b⟩
  cases b
  · exact prefix_side C Cs color t j
  · change χ ((schedule C Cs color)[j.val] (prefixApply (schedule C Cs color) j.val (C.vertex (t,color))))=_
    rw [(schedule_valid C Cs color _ (List.getElem_mem j.isLt)).2,prefix_side C Cs color t j]
    rfl

/-- The complete uniform tour vertex map is injective, before any graph
packaging. Different layers and before/after states cannot collide. -/
theorem layerTour_injective (C : CycleData X R χ r hr) (Cs : List (CycleData X R χ r hr)) (color : Bool) :
    Function.Injective (layerTour C Cs color) := by
  intro p q he
  rcases p with ⟨t,j,b⟩
  rcases q with ⟨z,k,c⟩
  have hj : j=k := congrArg Prod.fst he
  subst k
  have hx := congrArg Prod.snd he
  have hside := congrArg χ hx
  rw [layerTour_side C Cs color (t,j,b),layerTour_side C Cs color (z,j,c)] at hside
  change (if b then !flipN j.val color else flipN j.val color)=
    (if c then !flipN j.val color else flipN j.val color) at hside
  have hb : b=c := by
    cases b <;> cases c <;> try rfl
    · cases h : flipN j.val color <;> simp [h] at hside
    · cases h : flipN j.val color <;> simp [h] at hside
  subst c
  have hprefix : prefixApply (schedule C Cs color) j.val (C.vertex (t,color))=
      prefixApply (schedule C Cs color) j.val (C.vertex (z,color)) := by
    cases b
    · exact hx
    · have hh := congrArg ((schedule C Cs color)[j.val]) hx
      have hi := (schedule_valid C Cs color _ (List.getElem_mem j.isLt)).1
      simpa only [layerTour,↓reduceIte,hi] using hh
  have ht := applyWord_injective (valid_take (schedule_valid C Cs color) j.val) hprefix
  have tz : t=z := congrArg Prod.fst (vertex_injective C ht)
  subst z
  rfl

theorem applyWord_append (fs gs : List (X → X)) (x : X) :
    applyWord (fs++gs) x=applyWord gs (applyWord fs x) := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih => exact ih (f x)

theorem prefix_advance {fs : List (X → X)} (j : Fin fs.length) (x : X) :
    prefixApply fs (j.val+1) x=fs[j.val] (prefixApply fs j.val x) := by
  rw [prefixApply,List.take_succ_eq_append_getElem j.isLt,applyWord_append]
  rfl

/-- The actual horizontal-coordinate seam, including the last layer and the
last active clock coordinate, follows from the checked return. -/
theorem layerTour_outer_seam (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (color : Bool) (t : Fin r)
    (j : Fin (schedule C Cs color).length) (hj : j.val+1=(schedule C Cs color).length) :
    (layerTour C Cs color (t,j,true)).2=C.vertex (successor hr t,color) := by
  change (schedule C Cs color)[j.val]
    (prefixApply (schedule C Cs color) j.val (C.vertex (t,color)))=_
  rw [←prefix_advance (r:=r),hj]
  simp only [prefixApply,List.take_length,schedule_return,returnColor_advance]

/-- Interior horizontal steps preserve the actual X vertex exactly. -/
theorem layerTour_inner_seam (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (color : Bool) (t : Fin r)
    (j : Fin (schedule C Cs color).length) (hj : j.val+1<(schedule C Cs color).length) :
    (layerTour C Cs color (t,j,true)).2=
      (layerTour C Cs color (t,⟨j.val+1,hj⟩,false)).2 := by
  exact (prefix_advance (r:=r) j (C.vertex (t,color))).symm

theorem valid_reverse {fs : List (X → X)} (h : ValidWord χ fs) : ValidWord χ fs.reverse := by
  intro f hf
  exact h f (List.mem_reverse.mp hf)

theorem applyWord_inverse {fs : List (X → X)} (h : ValidWord χ fs) (x : X) :
    applyWord fs.reverse (applyWord fs x)=x := by
  induction fs generalizing x with
  | nil => rfl
  | cons f fs ih =>
    have ht : ValidWord χ fs := fun g hg => h g (List.mem_cons_of_mem f hg)
    simp only [List.reverse_cons,applyWord,applyWord_append,ih ht]
    exact (h f List.mem_cons_self).1 x

theorem applyWord_surjective {fs : List (X → X)} (h : ValidWord χ fs) : Function.Surjective (applyWord fs) := by
  intro x
  refine ⟨applyWord fs.reverse x,?_⟩
  have he := applyWord_inverse (valid_reverse h) x
  simpa only [List.reverse_reverse] using he

theorem flipN_not (n : Nat) (b : Bool) : flipN n (!b)= !flipN n b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => exact ih (!b)

theorem flipN_injective (n : Nat) : Function.Injective (flipN n) := by
  induction n with
  | zero => intro b c h; exact h
  | succ n ih =>
    intro b c h
    have hn := ih h
    cases b <;> cases c <;> simp_all

/-- All actual layer vertices are covered; no cardinality or Hamiltonicity
assumption about the output map is used. -/
theorem layerTour_surjective (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (color : Bool) : Function.Surjective (layerTour C Cs color) := by
  rintro ⟨j,x⟩
  let fs := schedule C Cs color
  have hp := valid_take (schedule_valid C Cs color) j.val
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
    have hf := schedule_valid C Cs color f (List.getElem_mem j.isLt)
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

theorem passiveWordA_length (Cs : List (CycleData X R χ r hr)) :
    (passiveWordA Cs).length=2*Cs.length := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih => simp only [passiveWordA,List.length_cons,ih]; omega

theorem passiveWordB_length (Cs : List (CycleData X R χ r hr)) :
    (passiveWordB Cs).length=2*Cs.length := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih => simp only [passiveWordB,List.length_cons,ih]; omega

theorem schedule_length (C : CycleData X R χ r hr)
    (Cs : List (CycleData X R χ r hr)) (color : Bool) :
    (schedule C Cs color).length=2*(Cs.length+1) := by
  cases color <;> simp only [schedule,Bool.false_eq_true,↓reduceIte,List.length_cons,
    passiveWordA_length,passiveWordB_length] <;> omega

#print axioms layerTour_inner_seam
#print axioms schedule_length
#print axioms layerTour_surjective
#print axioms layerTour_outer_seam
#print axioms layerTour_injective
#print axioms returnColor_orbit_closes
#print axioms returnColor_orbit_covers
#print axioms returnColor_orbit_injective
#print axioms returnZero_advance
#print axioms returnOne_advance
#print axioms passiveWordA_identity
#print axioms matchingB_involutive
end ErdePaths.PairedLayers
