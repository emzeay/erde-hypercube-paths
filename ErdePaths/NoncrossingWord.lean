import ErdePaths.PairedLayers

namespace ErdePaths.NoncrossingWord
open PairedLayers SquareLift

/-- Recursive nested forests of matched labels. A bracket contributes its
label at both ends; concatenation puts disjoint forests side by side. -/
inductive Forest (Label : Type) where
  | empty : Forest Label
  | concat : Forest Label → Forest Label → Forest Label
  | bracket : Label → Forest Label → Forest Label

def Forest.labels {Label : Type} : Forest Label → List Label
  | .empty => []
  | .concat u v => u.labels ++ v.labels
  | .bracket a u => a :: (u.labels ++ [a])

/-- Earliest layer acts first. This ordering makes an active A then B
contribute B ∘ A, even when the functions do not commute. -/
def Forest.interpret {Label X : Type} (σ : Label → X → X) : Forest Label → X → X
  | .empty,x => x
  | .concat u v,x => v.interpret σ (u.interpret σ x)
  | .bracket a u,x => σ a (u.interpret σ (σ a x))

/-- Every passive nested forest cancels, for arbitrary involutive labels,
including repeated labels and unrelated cyclic orders. -/
theorem Forest.identity {Label X : Type} (σ : Label → X → X)
    (hσ : ∀ a x, σ a (σ a x)=x) (u : Forest Label) (x : X) : u.interpret σ x=x := by
  induction u generalizing x with
  | empty => rfl
  | concat u v ihu ihv => exact (ihv (u.interpret σ x)).trans (ihu x)
  | bracket a u ihu =>
    change σ a (u.interpret σ (σ a x))=x
    rw [ihu,hσ]

/-- The recursive semantics equals the actual flattened layer word. -/
theorem Forest.flatten_interpret {Label X : Type} (σ : Label → X → X)
    (u : Forest Label) (x : X) : applyWord (u.labels.map σ) x=u.interpret σ x := by
  induction u generalizing x with
  | empty => rfl
  | concat u v ihu ihv =>
    simp only [Forest.labels,List.map_append,applyWord_append,ihu,ihv,Forest.interpret]
  | bracket a u ihu =>
    simp only [Forest.labels,List.map_cons,List.map_append,List.map_nil,
      applyWord,applyWord_append,ihu,Forest.interpret]

theorem Forest.flatten_identity {Label X : Type} (σ : Label → X → X)
    (hσ : ∀ a x, σ a (σ a x)=x) (u : Forest Label) (x : X) : applyWord (u.labels.map σ) x=x :=
  (u.flatten_interpret σ x).trans (u.identity σ hσ x)

/-- An explicit active chord surrounded by its interior and exterior passive
forests, after cutting the circular order immediately before the opening. -/
def activeWord {Label X : Type} (σ : Label → X → X) (A B : X → X)
    (inside outside : Forest Label) : List (X → X) :=
  A :: ((inside.labels.map σ) ++ B :: (outside.labels.map σ))

theorem activeWord_return {Label X : Type} (σ : Label → X → X)
    (hσ : ∀ a x, σ a (σ a x)=x) (A B : X → X)
    (inside outside : Forest Label) (x : X) :
    applyWord (activeWord σ A B inside outside) x=B (A x) := by
  simp only [activeWord,applyWord,applyWord_append,Forest.flatten_identity σ hσ]

theorem complementaryWord_return {Label X : Type} (σ : Label → X → X)
    (hσ : ∀ a x, σ a (σ a x)=x) (A B : X → X)
    (inside outside : Forest Label) (x : X) :
    applyWord (activeWord σ B A inside outside) x=A (B x) :=
  activeWord_return σ hσ B A inside outside x

/-- A proof-relevant recursive pairing grammar for a concrete layer-label
list. This describes nested/disjoint pairs without assuming cancellation. -/
inductive RecursivelyPaired {Label : Type} : List Label → Prop where
  | empty : RecursivelyPaired []
  | concat {u v : List Label} : RecursivelyPaired u → RecursivelyPaired v → RecursivelyPaired (u++v)
  | bracket (a : Label) {u : List Label} : RecursivelyPaired u → RecursivelyPaired (a::(u++[a]))

theorem recursivelyPaired_grammar {Label : Type} {xs : List Label}
    (h : RecursivelyPaired xs) : ∃ u : Forest Label, u.labels=xs := by
  induction h with
  | empty => exact ⟨.empty,rfl⟩
  | concat hu hv ihu ihv =>
    obtain ⟨u,hu⟩ := ihu
    obtain ⟨v,hv⟩ := ihv
    exact ⟨.concat u v,by simp only [Forest.labels,hu,hv]⟩
  | bracket a hu ihu =>
    obtain ⟨u,hu⟩ := ihu
    exact ⟨.bracket a u,by simp only [Forest.labels,hu]⟩

theorem grammar_recursivelyPaired {Label : Type} (u : Forest Label) : RecursivelyPaired u.labels := by
  induction u with
  | empty => exact .empty
  | concat u v ihu ihv => exact .concat ihu ihv
  | bracket a u ihu => exact .bracket a ihu

theorem recursivelyPaired_identity {Label X : Type} (σ : Label → X → X)
    (hσ : ∀ a x, σ a (σ a x)=x) {xs : List Label}
    (h : RecursivelyPaired xs) (x : X) : applyWord (xs.map σ) x=x := by
  obtain ⟨u,hu⟩ := recursivelyPaired_grammar h
  rw [←hu]
  exact u.flatten_identity σ hσ x

def Forest.pairCount {Label : Type} : Forest Label → Nat
  | .empty => 0
  | .concat u v => u.pairCount+v.pairCount
  | .bracket _ u => u.pairCount+1

theorem Forest.length_eq_twice_pairs {Label : Type} (u : Forest Label) :
    u.labels.length=2*u.pairCount := by
  induction u with
  | empty => rfl
  | concat u v ihu ihv =>
    simp only [Forest.labels,List.length_append,Forest.pairCount,ihu,ihv]
    omega
  | bracket a u ihu =>
    simp only [Forest.labels,List.length_cons,List.length_append,List.length_nil,
      Forest.pairCount,ihu]
    omega

theorem activeWord_length {Label X : Type} (σ : Label → X → X) (A B : X → X)
    (inside outside : Forest Label) :
    (activeWord σ A B inside outside).length=2*(inside.pairCount+outside.pairCount+1) := by
  simp only [activeWord,List.length_cons,List.length_append,List.length_map,
    Forest.length_eq_twice_pairs]
  omega

theorem Forest.flatten_valid {Label X : Type} {χ : X → Bool} (σ : Label → X → X)
    (hσ : ∀ a, (∀ x, σ a (σ a x)=x) ∧ (∀ x, χ (σ a x)= !χ x)) (u : Forest Label) :
    ValidWord χ (u.labels.map σ) := by
  intro f hf
  obtain ⟨a,_,ha⟩ := List.mem_map.mp hf
  subst f
  exact hσ a

theorem activeWord_valid {Label X : Type} {χ : X → Bool} (σ : Label → X → X)
    (hσ : ∀ a, (∀ x, σ a (σ a x)=x) ∧ (∀ x, χ (σ a x)= !χ x))
    (A B : X → X) (hA : (∀ x, A (A x)=x) ∧ (∀ x, χ (A x)= !χ x))
    (hB : (∀ x, B (B x)=x) ∧ (∀ x, χ (B x)= !χ x)) (inside outside : Forest Label) :
    ValidWord χ (activeWord σ A B inside outside) := by
  intro f hf
  simp only [activeWord,List.mem_cons,List.mem_append] at hf
  rcases hf with he | hi | he | ho
  · subst f; exact hA
  · exact inside.flatten_valid σ hσ f hi
  · subst f; exact hB
  · exact outside.flatten_valid σ hσ f ho

variable {Label X : Type} {R : X → X → Prop} {χ : X → Bool} {r : Nat} {hr : 0<r}

/-- The actual color-zero matching word, with arbitrary nested label forests. -/
def cycleWordZero (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) :=
  activeWord (fun a => matchingA (cycles a)) (matchingA C) (matchingB C) inside outside

def cycleWordOne (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) :=
  activeWord (fun a => matchingB (cycles a)) (matchingB C) (matchingA C) inside outside

theorem cycleWordZero_return (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (x : X) :
    applyWord (cycleWordZero C cycles inside outside) x=matchingB C (matchingA C x) :=
  activeWord_return _ (fun a => matchingA_involutive (cycles a)) _ _ inside outside x

theorem cycleWordOne_return (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (x : X) :
    applyWord (cycleWordOne C cycles inside outside) x=matchingA C (matchingB C x) :=
  activeWord_return _ (fun a => matchingB_involutive (cycles a)) _ _ inside outside x

/-- Exact active-clock action, with forward and backward motion on the two
sides made explicit rather than assuming transitivity. -/
theorem cycleWordZero_even (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (t : Fin r) :
    applyWord (cycleWordZero C cycles inside outside) (C.vertex (t,false))=
      C.vertex (successor hr t,false) := by
  rw [cycleWordZero_return,matchingA_vertex]
  exact matchingB_odd C t

theorem cycleWordZero_odd (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (t : Fin r) :
    applyWord (cycleWordZero C cycles inside outside) (C.vertex (t,true))=
      C.vertex (previous hr t,true) := by
  rw [cycleWordZero_return,matchingA_vertex]
  exact matchingB_even C t

theorem cycleWordOne_odd (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (t : Fin r) :
    applyWord (cycleWordOne C cycles inside outside) (C.vertex (t,true))=
      C.vertex (successor hr t,true) := by
  rw [cycleWordOne_return,matchingB_odd,matchingA_vertex]
  rfl

theorem cycleWordOne_even (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (t : Fin r) :
    applyWord (cycleWordOne C cycles inside outside) (C.vertex (t,false))=
      C.vertex (previous hr t,false) := by
  rw [cycleWordOne_return,matchingB_even,matchingA_vertex]
  rfl

theorem cycleWordZero_valid (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) : ValidWord χ (cycleWordZero C cycles inside outside) :=
  activeWord_valid _ (fun a => ⟨matchingA_involutive (cycles a),matchingA_flips (cycles a)⟩) _ _
    ⟨matchingA_involutive C,matchingA_flips C⟩ ⟨matchingB_involutive C,matchingB_flips C⟩ inside outside

theorem cycleWordOne_valid (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) : ValidWord χ (cycleWordOne C cycles inside outside) :=
  activeWord_valid _ (fun a => ⟨matchingB_involutive (cycles a),matchingB_flips (cycles a)⟩) _ _
    ⟨matchingB_involutive C,matchingB_flips C⟩ ⟨matchingA_involutive C,matchingA_flips C⟩ inside outside

def cycleWordColor (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :=
  if color then cycleWordOne C cycles inside outside else cycleWordZero C cycles inside outside

/-- Noncrossing forests have exactly the same return as the active clock;
this equality permits reuse of the already checked return-orbit proofs. -/
theorem cycleWordColor_function (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    applyWord (cycleWordColor C cycles inside outside color)=returnColor C [] color := by
  funext x
  cases color
  · exact (cycleWordZero_return C cycles inside outside x).trans (returnZero_formula C [] x).symm
  · exact (cycleWordOne_return C cycles inside outside x).trans (returnOne_formula C [] x).symm

theorem cycleWordColor_power (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) (t : Fin r) :
    power (applyWord (cycleWordColor C cycles inside outside color)) t.val
      (C.vertex (⟨0,hr⟩,color))=C.vertex (t,color) := by
  rw [cycleWordColor_function]
  exact returnColor_power C [] color t

theorem cycleWordColor_orbit_covers (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) (x : X) (hx : χ x=color) :
    ∃ t : Fin r, power (applyWord (cycleWordColor C cycles inside outside color)) t.val
      (C.vertex (⟨0,hr⟩,color))=x := by
  rw [cycleWordColor_function]
  exact returnColor_orbit_covers C [] color x hx

theorem cycleWordColor_orbit_injective (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    Function.Injective (fun t : Fin r => power
      (applyWord (cycleWordColor C cycles inside outside color)) t.val (C.vertex (⟨0,hr⟩,color))) := by
  rw [cycleWordColor_function]
  exact returnColor_orbit_injective C [] color

theorem cycleWordColor_orbit_closes (C : CycleData X R χ r hr) (cycles : Label → CycleData X R χ r hr)
    (inside outside : Forest Label) (color : Bool) :
    power (applyWord (cycleWordColor C cycles inside outside color)) r
      (C.vertex (⟨0,hr⟩,color))=C.vertex (⟨0,hr⟩,color) := by
  rw [cycleWordColor_function]
  exact returnColor_orbit_closes C [] color

#print axioms cycleWordColor_orbit_covers
#print axioms cycleWordColor_orbit_injective
#print axioms cycleWordColor_orbit_closes
#print axioms activeWord_length
#print axioms cycleWordZero_valid
#print axioms Forest.identity
#print axioms activeWord_return
#print axioms recursivelyPaired_identity
#print axioms cycleWordZero_return
#print axioms cycleWordZero_even
#print axioms cycleWordZero_odd
end ErdePaths.NoncrossingWord
