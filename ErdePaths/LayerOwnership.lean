import ErdePaths.LayerTour

namespace ErdePaths.LayerOwnership
open SquareLift PairedLayers SubdividedWiggle
variable {X : Type} {R : X → X → Prop} {χ : X → Bool} {r q : Nat} {hr : 0<r}

/-- The two actual alternating matchings of a displayed input cycle. -/
def choose (C : CycleData X R χ r hr) (a : Bool) : X → X :=
  if a then matchingB C else matchingA C

theorem choose_flips (C : CycleData X R χ r hr) (a : Bool) (x : X) :
    χ (choose C a x)= !χ x := by
  cases a
  · exact matchingA_flips C x
  · exact matchingB_flips C x

theorem choose_involutive (C : CycleData X R χ r hr) (a : Bool) (x : X) :
    choose C a (choose C a x)=x := by
  cases a
  · exact matchingA_involutive C x
  · exact matchingB_involutive C x

theorem previous_ne (h2 : 2≤r) (t : Fin r) : previous hr t≠t := by
  intro he
  have hs := next_previous hr t
  rw [he] at hs
  exact successor_ne hr h2 t hs

/-- Each matching edge is labeled once, at its actual χ-false endpoint. -/
def matchingPair (C : CycleData X R χ r hr) (a : Bool) (t : Fin r) : X×X :=
  (C.vertex (t,false),choose C a (C.vertex (t,false)))

theorem matchingPair_unique (h2 : 2≤r) (C : CycleData X R χ r hr)
    (a b : Bool) (t z : Fin r) (he : SameEdge (matchingPair C a t) (matchingPair C b z)) :
    a=b ∧ t=z := by
  rcases he with he | he
  · have ht := congrArg Prod.fst he
    have htz : t=z := congrArg Prod.fst (vertex_injective C ht)
    subst z
    have hm := congrArg Prod.snd he
    have hab : a=b := by
      cases a <;> cases b
      · rfl
      · have hp : t=previous hr t := by
          simp only [matchingPair,choose,Bool.false_eq_true,↓reduceIte,matchingA_vertex,matchingB_even] at hm
          exact congrArg Prod.fst (vertex_injective C hm)
        exact False.elim (previous_ne h2 t hp.symm)
      · have hp : previous hr t=t := by
          simp only [matchingPair,choose,Bool.false_eq_true,↓reduceIte,matchingA_vertex,matchingB_even] at hm
          exact congrArg Prod.fst (vertex_injective C hm)
        exact False.elim (previous_ne h2 t hp)
      · rfl
    exact ⟨hab,rfl⟩
  · have hc := congrArg (fun e : X×X => χ e.1) he
    simp only [matchingPair,choose_flips,C.bipartition] at hc
    cases hc

abbrev HostLabel (q r : Nat) := (Fin q × Bool × Fin r) ⊕ (Fin q × Fin r × Bool)

/-- Actual edges of the COMMON host, before any output tour is defined.
Layer cycles may differ and may repeat. The active clock only enumerates X. -/
def decode (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (hq : 0<q) : HostLabel q r → (Fin q×X)×(Fin q×X)
  | .inl (j,a,t) => ((j,(layers j).vertex (t,false)),
      (j,choose (layers j) a ((layers j).vertex (t,false))))
  | .inr (j,t,b) => ((j,C.vertex (t,b)),(successor hq j,C.vertex (t,b)))

def HostAdjacent (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (hq : 0<q) (u v : Fin q×X) : Prop :=
  ∃ e : HostLabel q r, SameEdge (decode C layers hq e) (u,v)

private theorem no_constant_arc (hq : 0<q) (h2 : 2≤q) (j k : Fin q) :
    ¬SameEdge (j,j) (k,successor hq k) := by
  intro he
  rcases he with he | he
  · have h1 := congrArg Prod.fst he
    have h2' := congrArg Prod.snd he
    exact successor_ne hq h2 k (h2'.symm.trans h1)
  · have h1 := congrArg Prod.fst he
    have h2' := congrArg Prod.snd he
    exact successor_ne hq h2 k (h1.symm.trans h2')

/-- Undirected host labels have no duplicates, including both cyclic seams. -/
theorem decode_unique (h2 : 2≤r) (h4 : 4≤q)
    (C : CycleData X R χ r hr) (layers : Fin q → CycleData X R χ r hr)
    (e f : HostLabel q r) (he : SameEdge (decode C layers (by omega) e)
      (decode C layers (by omega) f)) : e=f := by
  cases e with
  | inl e =>
    rcases e with ⟨j,a,t⟩
    cases f with
    | inl f =>
      rcases f with ⟨k,b,z⟩
      have hj : j=k := by
        rcases he with he | he <;> exact congrArg (fun x => x.1.1) he
      subst k
      have hm := map_sameEdge Prod.snd he
      change SameEdge (matchingPair (layers j) a t) (matchingPair (layers j) b z) at hm
      obtain ⟨hab,htz⟩ := matchingPair_unique h2 (layers j) a b t z hm
      subst b; subst z; rfl
    | inr f =>
      rcases f with ⟨k,z,b⟩
      have hm := map_sameEdge Prod.fst he
      exact False.elim (no_constant_arc (by omega) (by omega) j k hm)
  | inr e =>
    rcases e with ⟨j,t,a⟩
    cases f with
    | inl f =>
      rcases f with ⟨k,b,z⟩
      have hm := map_sameEdge Prod.fst (sameEdge_symm he)
      exact False.elim (no_constant_arc (by omega) (by omega) k j hm)
    | inr f =>
      rcases f with ⟨k,z,b⟩
      have hj := Wiggle.cyclic_arc_unique (show 3≤q by omega) j k (map_sameEdge Prod.fst he)
      subst k
      have hx : C.vertex (t,a)=C.vertex (z,b) := by
        rcases he with he | he <;> exact congrArg (fun x => x.1.2) he
      have hp := vertex_injective C hx
      have ht := congrArg Prod.fst hp
      have hb := congrArg Prod.snd hp
      change t=z at ht
      change a=b at hb
      subst z; subst b; rfl

#print axioms matchingPair_unique
#print axioms decode_unique
end ErdePaths.LayerOwnership
