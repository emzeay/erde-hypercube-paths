import ErdePaths.LayerPartition

namespace ErdePaths.AACUnfold
open PairedLayers LayerPartition
variable {B X : Type} {R : X → X → Prop} {χ : X → Bool} {r q : Nat} {hr : 0<r}

/-- Half-open physical AAC interiors. These geometric laws concern only base
occurrences, never an output cycle. Actual torus construction must supply them. -/
structure Intervals (B : Type) (q : Nat) where
  interior : Fin q → Nat
  mark : Fin q → B
  mark_injective : Function.Injective mark
  physical : ((j : Fin q) × Fin (interior j)) → B
  mark_exclusion : ∀ o j, physical o ≠ mark j
  collision : ∀ o p, physical o=physical p → o=p ∨ o.1.val%2≠p.1.val%2

abbrev Occurrence (I : Intervals B q) := (j : Fin q) × Fin (I.interior j)
abbrev Position (I : Intervals B q) (r : Nat) :=
  (Fin r × Fin q × Bool) ⊕ (Occurrence I × Fin r)

/-- Contracted mark vertices and expanded interval interiors have distinct
positions. Interior vertices keep the actual departure J vertex. -/
def vertex (I : Intervals B q) (C : CycleData X R χ r hr)
    (layers : Fin q → CycleData X R χ r hr) (selectors : Fin q → Bool) (color : Bool) :
    Position I r → B×X
  | .inl p => (I.mark p.2.1,(commonTour C layers selectors color p).2)
  | .inr (o,t) => (I.physical o,departure C layers selectors color o.1 t)

theorem flipN_mod (n : Nat) (b : Bool) :
    flipN n b = if n%2=0 then b else !b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change flipN n (!b)=_
    rw [ih]
    have hlt : n%2<2 := Nat.mod_lt n (by decide)
    by_cases hn : n%2=0
    · have hs : (n+1)%2=1 := by omega
      simp [hn,hs]
    · have hs : (n+1)%2=0 := by omega
      simp [hn,hs]

theorem flipN_phase {a b : Nat} (color : Bool) (he : flipN a color=flipN b color) :
    a%2=b%2 := by
  rw [flipN_mod,flipN_mod] at he
  have ha : a%2<2 := Nat.mod_lt a (by decide)
  have hb : b%2<2 := Nat.mod_lt b (by decide)
  by_cases h0 : a%2=0 <;> by_cases h1 : b%2=0
  · omega
  · simp only [h0,h1,↓reduceIte] at he
    cases color <;> cases he
  · simp only [h0,h1,↓reduceIte] at he
    cases color <;> cases he
  · omega

/-- Physical repeated AAC vertices in opposite interval parities cannot
collide in one unfolded output. No output injectivity is an assumption. -/
theorem vertex_injective (I : Intervals B q) (C : CycleData X R χ r hr)
    (layers : Fin q → CycleData X R χ r hr) (selectors : Fin q → Bool) (color : Bool) :
    Function.Injective (vertex I C layers selectors color) := by
  intro p z he
  cases p with
  | inl p =>
    cases z with
    | inl z =>
      have hj := I.mark_injective (congrArg Prod.fst he)
      have hx := congrArg Prod.snd he
      have ht := commonTour_injective C layers selectors color (Prod.ext hj hx)
      exact congrArg Sum.inl ht
    | inr z =>
      exact False.elim (I.mark_exclusion z.1 p.2.1 (congrArg Prod.fst he).symm)
  | inr p =>
    cases z with
    | inl z =>
      exact False.elim (I.mark_exclusion p.1 z.2.1 (congrArg Prod.fst he))
    | inr z =>
      have hb := congrArg Prod.fst he
      have hx := congrArg Prod.snd he
      rcases I.collision p.1 z.1 hb with ho | hpar
      · have hh : p=z := by
          rcases p with ⟨o,t⟩
          rcases z with ⟨u,s⟩
          change o=u at ho
          subst u
          have ht := departure_injective C layers selectors color o.1 hx
          exact Prod.ext rfl ht
        exact congrArg Sum.inr hh
      · have hs := congrArg χ hx
        change χ (departure C layers selectors color p.1.1 p.2)=
          χ (departure C layers selectors color z.1.1 z.2) at hs
        rw [departure_side C layers selectors color p.1.1 p.2,
          departure_side C layers selectors color z.1.1 z.2] at hs
        have hflip : flipN p.1.1.val color=flipN z.1.1.val color := by
          have hh := congrArg Bool.not hs
          simpa only [Bool.not_not] using hh
        exact False.elim (hpar (flipN_phase color hflip))

#print axioms vertex_injective
#print axioms flipN_phase
end ErdePaths.AACUnfold
