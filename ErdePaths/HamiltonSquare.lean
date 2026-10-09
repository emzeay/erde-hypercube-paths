import ErdePaths.HamiltonData
import ErdePaths.Profile

namespace ErdePaths.HamiltonSquare
open SquareLift SourceClock HamiltonData

theorem negate_successor {N : Nat} (hN : 0<N) (i : Fin N) :
    negate hN (successor hN i) = predecessor hN (negate hN i) := by
  by_cases hi : i.val+1<N
  · have hs : successor hN i = ⟨i.val+1,hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    have hh := congrArg (predecessor hN) (successor_backward_step hN ⟨0,hN⟩ hi)
    rw [predecessor_successor] at hh
    simpa [negate,hs] using hh
  · have hv : i.val=N-1 := by have := i.isLt; omega
    have hs : successor hN i=⟨0,hN⟩ := by apply Fin.ext; simp [successor,show i.val+1=N by omega]
    rw [hs]
    have hil : i=⟨N-1,by omega⟩ := Fin.ext hv
    simp only [negate,hil,backward_last,backward_zero,predecessor_successor]

def tourMacro {N : Nat} (hN : 0<N) (b : Bool) (t : Fin (N*N)) : MacroPosition N :=
  if b then .inr (negate hN (pairCoordinates hN t).1,(pairCoordinates hN t).2)
  else .inl (pairCoordinates hN t)

theorem plus_next_macro {V : Type} {N : Nat} (hN : 0<N) (cycle : Fin N → V)
    (a : Fin N × Fin N) :
    plusVertex hN cycle (Profile.coordinateNext hN a) = plusMacro hN cycle a.1 a.2.succ := by
  by_cases hr : a.2.val+1<N
  · have hs : successor hN a.2=⟨a.2.val+1,hr⟩ := Fin.ext (Nat.mod_eq_of_lt hr)
    simp [Profile.coordinateNext,hr,plusVertex,plusMacro,hs]
  · simp [Profile.coordinateNext,hr,plusVertex,plusMacro,backward_zero]

theorem minus_next_macro {V : Type} {N : Nat} (hN : 0<N) (cycle : Fin N → V)
    (a : Fin N × Fin N) :
    minusVertex hN cycle (negate hN (Profile.coordinateNext hN a).1,
      (Profile.coordinateNext hN a).2) = minusMacro hN cycle (negate hN a.1) a.2.succ := by
  by_cases hr : a.2.val+1<N
  · have hs : successor hN a.2=⟨a.2.val+1,hr⟩ := Fin.ext (Nat.mod_eq_of_lt hr)
    simp [Profile.coordinateNext,hr,minusVertex,minusMacro,hs]
  · simp [Profile.coordinateNext,hr,minusVertex,minusMacro,forward_zero,negate_successor]

theorem tour_edge_macro {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (b : Bool) (t : Fin (N*N)) :
    ((squareClock hN C b).cycle t,(squareClock hN C b).cycle (successor (Nat.mul_pos hN hN) t)) =
      macroStep hN C.cycle (tourMacro hN b t) := by
  cases b
  · simp only [squareClock,plusTour,Profile.pairCoordinates_next,tourMacro,Bool.false_eq_true,↓reduceIte,macroStep]
    rw [plus_next_macro]
    congr 1
    simp [plusMacro,plusVertex,(pairCoordinates hN t).2.isLt]
  · simp only [squareClock,minusTour,Profile.pairCoordinates_next,tourMacro,↓reduceIte,macroStep]
    rw [minus_next_macro]
    congr 1
    simp [minusMacro,minusVertex,(pairCoordinates hN t).2.isLt]

def cycle {V : Type} {R : V → V → Prop} {N : Nat} (hN : 0<N)
    (C : CycleData V R N hN) (hs : ∀ u v, R u v → R v u) (b : Bool) :
    CycleData (V×V) (ProductAdjacent R) (N*N) (Nat.mul_pos hN hN) where
  toClockData := squareClock hN C.toClockData b
  adjacent t := by
    have hm := tour_edge_macro hN C.toClockData b t
    have ha := macroStep_adjacent hN hs C.adjacent (tourMacro hN b t)
    simpa only [←hm] using ha

def familyDecode {V : Type} {R : V → V → Prop} {m N : Nat} {hN : 0<N}
    (d : DecompositionData V R m N hN) (f : Fin m) (e : TorusEdgeLabel N) :
    (V×V)×(V×V) := decode hN ((d.cycles f).cycle) e

/-- Torus ownership survives across distinct Hamilton factors: no product edge
can be represented by different factor/torus-edge labels. -/
theorem familyDecode_injective {V : Type} {R : V → V → Prop} {m N : Nat} {hN : 0<N}
    (d : DecompositionData V R m N hN) (h3 : 3 ≤ N)
    {f g : Fin m} {a b : TorusEdgeLabel N}
    (he : SameEdge (familyDecode d f a) (familyDecode d g b)) : f = g ∧ a = b := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp only [SameEdge,familyDecode,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have hfg := d.unique f a.2 g b.2 (Or.inl (Prod.ext he.1.1 he.2.1))
        have hrow := he.1.2
        rw [← hfg.1] at hrow
        exact ⟨hfg.1,congrArg Sum.inl (Prod.ext (cycle_injective (d.cycles f) hrow) hfg.2)⟩
      · have hfg := d.unique f a.2 g b.2 (Or.inr (Prod.ext he.1.1 he.2.1))
        have hrow := he.1.2
        rw [← hfg.1] at hrow
        exact ⟨hfg.1,congrArg Sum.inl (Prod.ext (cycle_injective (d.cycles f) hrow) hfg.2)⟩
    | inr b =>
      simp only [SameEdge,familyDecode,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have hh := cycle_injective (d.cycles f) (he.2.1.trans he.1.1.symm)
        exact False.elim (successor_ne hN (by omega) a.2 hh)
      · have hh := cycle_injective (d.cycles f) (he.2.1.trans he.1.1.symm)
        exact False.elim (successor_ne hN (by omega) a.2 hh)
  | inr a =>
    cases b with
    | inl b =>
      simp only [SameEdge,familyDecode,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have hh := cycle_injective (d.cycles g) (he.2.1.symm.trans he.1.1)
        exact False.elim (successor_ne hN (by omega) b.2 hh)
      · have hh := cycle_injective (d.cycles g) (he.1.1.symm.trans he.2.1)
        exact False.elim (successor_ne hN (by omega) b.2 hh)
    | inr b =>
      simp only [SameEdge,familyDecode,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have hfg := d.unique f a.2 g b.2 (Or.inl (Prod.ext he.1.2 he.2.2))
        have hcol := he.1.1
        rw [← hfg.1] at hcol
        exact ⟨hfg.1,congrArg Sum.inr (Prod.ext (cycle_injective (d.cycles f) hcol) hfg.2)⟩
      · have hfg := d.unique f a.2 g b.2 (Or.inr (Prod.ext he.1.2 he.2.2))
        have hcol := he.1.1
        rw [← hfg.1] at hcol
        exact ⟨hfg.1,congrArg Sum.inr (Prod.ext (cycle_injective (d.cycles f) hcol) hfg.2)⟩

/-- Every actual product-graph edge belongs to one of the factor tori. -/
theorem familyDecode_cover {V : Type} {R : V → V → Prop} {m N : Nat} {hN : 0<N}
    (d : DecompositionData V R m N hN) (u v : V×V) (huv : ProductAdjacent R u v) :
    ∃ f e, SameEdge (familyDecode d f e) (u,v) := by
  rcases huv with huv | huv
  · obtain ⟨f,i,he⟩ := d.cover u.2 v.2 huv.2
    obtain ⟨col,hcol⟩ := cycle_surjective (d.cycles f) u.1
    refine ⟨f,.inr (col,i),?_⟩
    simp only [SameEdge,Prod.mk.injEq] at he
    rcases he with he | he
    · left
      simp only [familyDecode,decode]
      exact Prod.ext (Prod.ext hcol he.1) (Prod.ext (hcol.trans huv.1) he.2)
    · right
      simp only [familyDecode,decode]
      exact Prod.ext (Prod.ext (hcol.trans huv.1) he.1) (Prod.ext hcol he.2)
  · obtain ⟨f,i,he⟩ := d.cover u.1 v.1 huv.2
    obtain ⟨row,hrow⟩ := cycle_surjective (d.cycles f) u.2
    refine ⟨f,.inl (row,i),?_⟩
    simp only [SameEdge,Prod.mk.injEq] at he
    rcases he with he | he
    · left
      simp only [familyDecode,decode]
      exact Prod.ext (Prod.ext he.1 hrow) (Prod.ext he.2 (hrow.trans huv.1))
    · right
      simp only [familyDecode,decode]
      exact Prod.ext (Prod.ext he.1 (hrow.trans huv.1)) (Prod.ext he.2 hrow)


theorem tourMacro_injective {N : Nat} (hN : 0<N) (b c : Bool) (t u : Fin (N*N))
    (h : tourMacro hN b t = tourMacro hN c u) : b=c ∧ t=u := by
  have hi (a a' : Fin N × Fin N) (hh : a=a') : pairIndex a=pairIndex a' := congrArg pairIndex hh
  cases b <;> cases c <;> simp only [tourMacro,Bool.false_eq_true,↓reduceIte] at h
  · have hh := hi _ _ (Sum.inl.inj h)
    rw [pairIndex_coordinates,pairIndex_coordinates] at hh
    exact ⟨rfl,hh⟩
  · cases h
  · cases h
  · have hp := Sum.inr.inj h
    have hh : pairCoordinates hN t = pairCoordinates hN u := by
      apply Prod.ext
      · have hn := congrArg (fun z => negate hN z.1) hp
        simpa only [negate_involutive] using hn
      · have hs := congrArg (fun z : Fin N × Fin N => z.2) hp
        exact hs
    have ht := hi _ _ hh
    rw [pairIndex_coordinates,pairIndex_coordinates] at ht
    exact ⟨rfl,ht⟩

theorem tourMacro_surjective {N : Nat} (hN : 0<N) (a : MacroPosition N) :
    ∃ b t, tourMacro hN b t = a := by
  cases a with
  | inl a => exact ⟨false,pairIndex a,by simp [tourMacro,pairCoordinates_index]⟩
  | inr a => exact ⟨true,pairIndex (negate hN a.1,a.2),by simp [tourMacro,pairCoordinates_index,negate_involutive]⟩

def factorIndex {m : Nat} (a : Fin m × Bool) : Fin (2*m) :=
  ⟨2*a.1.val+(if a.2 then 1 else 0),by have := a.1.isLt; cases a.2 <;> simp <;> omega⟩

def factorCoordinates {m : Nat} (i : Fin (2*m)) : Fin m × Bool :=
  (⟨i.val/2,by have := i.isLt; omega⟩,decide (i.val%2=1))

theorem factorCoordinates_index {m : Nat} (a : Fin m × Bool) :
    factorCoordinates (factorIndex a)=a := by
  apply Prod.ext
  · apply Fin.ext; cases hb : a.2 <;> simp [factorCoordinates,factorIndex,hb] <;> omega
  · cases hb : a.2 <;> simp [factorCoordinates,factorIndex,hb] <;> omega

theorem factorIndex_coordinates {m : Nat} (i : Fin (2*m)) :
    factorIndex (factorCoordinates i)=i := by
  apply Fin.ext
  have hm : i.val%2<2 := Nat.mod_lt _ (by omega)
  by_cases hh : i.val%2=1 <;> simp [factorCoordinates,factorIndex,hh] <;> omega

theorem cyclicEdge_decodes {V : Type} {R : V → V → Prop} {m N : Nat} {hN : 0<N}
    (d : DecompositionData V R m N hN) (f : Fin m) (b : Bool) (t : Fin (N*N)) :
    SameEdge ((cycle hN (d.cycles f) d.symmetric b).cycle t,
      (cycle hN (d.cycles f) d.symmetric b).cycle (successor (Nat.mul_pos hN hN) t))
      (familyDecode d f (macroLabel hN (tourMacro hN b t))) := by
  rw [show ((cycle hN (d.cycles f) d.symmetric b).cycle t,
      (cycle hN (d.cycles f) d.symmetric b).cycle (successor (Nat.mul_pos hN hN) t)) =
        macroStep hN (d.cycles f).cycle (tourMacro hN b t) from tour_edge_macro hN (d.cycles f).toClockData b t]
  exact macroStep_decodes hN (d.cycles f).cycle _

/-- The standard square produces 2m actual Hamilton factors, partitioning all
actual product edges once. No output decomposition is supplied as a premise. -/
def square {V : Type} {R : V → V → Prop} {m N : Nat} {hN : 0<N}
    (d : DecompositionData V R m N hN) (h4 : 4≤N) :
    DecompositionData (V×V) (ProductAdjacent R) (2*m) (N*N) (Nat.mul_pos hN hN) where
  cycles i := cycle hN (d.cycles (factorCoordinates i).1) d.symmetric (factorCoordinates i).2
  symmetric := fun _ _ h => productAdjacent_symm d.symmetric h
  loopfree u h := by
    rcases h with h | h
    · exact d.loopfree u.2 h.2
    · exact d.loopfree u.1 h.2
  cover u v huv := by
    obtain ⟨f,e,he⟩ := familyDecode_cover d u v huv
    obtain ⟨a,ha⟩ := macroLabel_surjective hN e
    obtain ⟨b,t,ht⟩ := tourMacro_surjective hN a
    refine ⟨factorIndex (f,b),t,?_⟩
    simp only [factorCoordinates_index]
    have hc := cyclicEdge_decodes d f b t
    rw [ht,ha] at hc
    exact sameEdge_trans hc he
  unique i t j u he := by
    have hi := cyclicEdge_decodes d (factorCoordinates i).1 (factorCoordinates i).2 t
    have hj := cyclicEdge_decodes d (factorCoordinates j).1 (factorCoordinates j).2 u
    have hd := sameEdge_trans (sameEdge_symm hi) (sameEdge_trans he hj)
    obtain ⟨hf,hl⟩ := familyDecode_injective d (by omega) hd
    have hm := macroLabel_injective hN hl
    obtain ⟨hb,htu⟩ := tourMacro_injective hN _ _ _ _ hm
    have hc : factorCoordinates i = factorCoordinates j := Prod.ext hf hb
    have hij := congrArg factorIndex hc
    rw [factorIndex_coordinates,factorIndex_coordinates] at hij
    exact ⟨hij,htu⟩

#print axioms square
#print axioms familyDecode_injective
#print axioms cycle
end ErdePaths.HamiltonSquare
