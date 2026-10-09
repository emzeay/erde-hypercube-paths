import ErdePaths.AACMerge
import ErdePaths.CubeCycle

namespace ErdePaths.AACChain
open SquareLift SourceClock AACTransition AACMerge

private theorem coordinates_next {K : Nat} (hK : 0<K) (n : Fin (2*K)) :
    CubeCycle.coordinates hK (successor (by omega) n)=
      loopNext hK (CubeCycle.coordinates hK n) := by
  rw [←CubeCycle.index_coordinates hK n]
  rcases hc : CubeCycle.coordinates hK n with ⟨i,b⟩
  rw [CubeCycle.coordinates_index]
  cases b
  · rw [CubeCycle.index_even_next,CubeCycle.coordinates_index]
    rfl
  · rw [CubeCycle.index_odd_next,CubeCycle.coordinates_index]
    rfl

/-- Concrete numeric baseline circuit, with forced cyclic successor. -/
def baselineOrbit {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (label : Fin B) :
    Orbit (State K B) (transition hK hB (fun w => t w.1)) (2*K) (by omega) where
  point n := baselineLoop hK hB t label (CubeCycle.coordinates hK n)
  injective := by
    intro n m h
    have hp := baselineLoop_injective hK hB t (a₁ := (label,CubeCycle.coordinates hK n)) (a₂ := (label,CubeCycle.coordinates hK m)) h
    have hc := congrArg Prod.snd hp
    have hn := congrArg (CubeCycle.index hK) hc
    simpa only [CubeCycle.index_coordinates] using hn
  next n := by rw [baselineLoop_next hK hB t hb,coordinates_next]

private theorem rev_successor {N : Nat} (hN : 0<N) (n : Fin N) :
    (successor hN n).rev=predecessor hN n.rev := by
  apply Fin.ext
  simp only [Fin.val_rev, predecessor]
  by_cases hn : n.val+1<N
  · have hs : (successor hN n).val=n.val+1 := Nat.mod_eq_of_lt hn
    change N-((successor hN n).val+1)=(N-1+(N-(n.val+1)))%N
    rw [hs]
    have he : N-1+(N-(n.val+1))=N+(N-((n.val+1)+1)) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  · have hn' : n.val+1=N := by have := n.isLt; omega
    have hs : (successor hN n).val=0 := by simp [successor,hn']
    change N-((successor hN n).val+1)=(N-1+(N-(n.val+1)))%N
    rw [hs]
    have he : N-(n.val+1)=0 := by omega
    simp only [he,Nat.add_zero,Nat.mod_eq_of_lt (show N-1<N by omega)]

private theorem inverse_orbit_step {X : Type} {T I : X → X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (hi : ∀ s, I (T s)=s) (n : Fin N) :
    I (C.point n)=C.point (predecessor hN n) := by
  have h := C.next (predecessor hN n)
  rw [successor_predecessor] at h
  have hh := congrArg I h
  rw [hi] at hh
  exact hh.symm

/-- An actual reverse traversal for the same physical baseline circuit. -/
def reverseBaseline {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (label : Fin B) :
    Orbit (State K B) (transition hK hB (fun w => t w.1)) (2*K) (by omega) where
  point n := atPair (fun w => t w.1) ((baselineOrbit hK hB t hb label).point n.rev)
  injective := by
    intro n m h
    have hh := congrArg (atPair (fun w => t w.1)) h
    simp only [atPair_involutive] at hh
    have hn := (baselineOrbit hK hB t hb label).injective hh
    have hr := congrArg Fin.rev hn
    simpa only [Fin.rev_rev] using hr
  next n := by
    have hp (s : State K B) : transition hK hB (fun w => t w.1) (atPair (fun w => t w.1) s)=
        atPair (fun w => t w.1) (inverseTransition hK hB (fun w => t w.1) s) := by
      simp only [transition,inverseTransition,atPair_involutive]
    rw [hp,inverse_orbit_step _ (inverse_transition hK hB _) n.rev,rev_successor]


/-- Distinct baseline labels give disjoint positive directed circuits. -/
theorem baseline_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) {a b : Fin B} (hab : a≠b) (i j : Fin (2*K)) :
    (baselineOrbit hK hB t hb a).point i ≠ (baselineOrbit hK hB t hb b).point j := by
  intro h
  have hh := baselineLoop_injective hK hB t
    (a₁ := (a,CubeCycle.coordinates hK i)) (a₂ := (b,CubeCycle.coordinates hK j)) h
  exact hab (congrArg Prod.fst hh)

/-- The reverse circuit never shares a directed state with any positive circuit. -/
theorem positive_reverse_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (a b : Fin B) (i j : Fin (2*K)) :
    (baselineOrbit hK hB t hb a).point i ≠ (reverseBaseline hK hB t hb b).point j := by
  intro h
  have hp := baselineLoop_positive hK hB t a (CubeCycle.coordinates hK i)
  have hq := baselineLoop_positive hK hB t b (CubeCycle.coordinates hK j.rev)
  have hn := AACTransition.positive_reverse_disjoint t _ hq
  apply hn
  change PositiveState t ((reverseBaseline hK hB t hb b).point j)
  rw [←h]
  exact hp

theorem reverse_disjoint {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) {a b : Fin B} (hab : a≠b) (i j : Fin (2*K)) :
    (reverseBaseline hK hB t hb a).point i ≠ (reverseBaseline hK hB t hb b).point j := by
  intro h
  have hh := congrArg (atPair (fun w => t w.1)) h
  simp only [reverseBaseline,atPair_involutive] at hh
  exact baseline_disjoint hK hB t hb hab i.rev j.rev hh

/-- The numeric forward/reverse clocks exhaust actual directed states. -/
theorem baseline_covers {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (s : State K B) :
    ∃label, (∃i, (baselineOrbit hK hB t hb label).point i=s) ∨
      (∃i, (reverseBaseline hK hB t hb label).point i=s) := by
  rcases positive_or_reverse t s with hp | hp
  · obtain ⟨label,p,he⟩ := baselineLoop_covers_positive hK hB t s hp
    refine ⟨label,Or.inl ⟨CubeCycle.index hK p,?_⟩⟩
    simpa only [baselineOrbit,CubeCycle.coordinates_index] using he
  · obtain ⟨label,p,he⟩ := baselineLoop_covers_positive hK hB t _ hp
    refine ⟨label,Or.inr ⟨(CubeCycle.index hK p).rev,?_⟩⟩
    simp only [reverseBaseline,baselineOrbit,Fin.rev_rev,CubeCycle.coordinates_index,he,atPair_involutive]

/-- A literal turn flip leaves any clock avoiding the four actual ports intact. -/
theorem away_flip {K B N : Nat} (hK : 0<K) (hB : 0<B) (hN : 0<N)
    (turns : Grid K B → Bool) (g : Grid K B)
    (C : Orbit (State K B) (transition hK hB turns) N hN)
    (ha : ∀i, C.point i≠(g.1,g.2,Port.up))
    (hb : ∀i, C.point i≠(g.1,g.2,Port.down))
    (hc : ∀i, C.point i≠(g.1,g.2,Port.left))
    (hd : ∀i, C.point i≠(g.1,g.2,Port.right)) :
    ∃D : Orbit (State K B) (transition hK hB (flippedTurns turns g)) N hN,
      ∀i, D.point i=C.point i := by
  let J := (C.outside_splice _ _ ha hb).outside_splice _ _ hc hd
  have he : splice (splice (transition hK hB turns) (g.1,g.2,Port.up) (g.1,g.2,Port.down))
      (g.1,g.2,Port.left) (g.1,g.2,Port.right)=transition hK hB (flippedTurns turns g) := by
    funext s
    exact (flip_transition hK hB turns g s).symm
  rw [←he]
  exact ⟨J,fun _ => rfl⟩

/-- Exact baseline membership of all four incoming ports at column zero. -/
theorem zero_ports {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) (j : Fin B) :
    (baselineOrbit hK hB t hb j).point (CubeCycle.index hK (⟨0,hK⟩,false))=(⟨0,hK⟩,j,.down) ∧
    (baselineOrbit hK hB t hb (successor hB j)).point (CubeCycle.index hK (⟨0,hK⟩,true))=(⟨0,hK⟩,j,.right) ∧
    (reverseBaseline hK hB t hb j).point (CubeCycle.index hK (⟨0,hK⟩,false)).rev=(⟨0,hK⟩,j,.left) ∧
    (reverseBaseline hK hB t hb (successor hB j)).point (CubeCycle.index hK (⟨0,hK⟩,true)).rev=(⟨0,hK⟩,j,.up) := by
  have hf (a : Fin B) : baselinePoint hB t a ⟨0,hK⟩=(⟨0,hK⟩,a) := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [baselinePoint,drift_zero,forward,Nat.mod_eq_of_lt a.isLt]
  simp [baselineOrbit,reverseBaseline,CubeCycle.coordinates_index,Fin.rev_rev,
    baselineLoop,hf,transition,atPair,cross,pair,ht,predecessor_successor]

/-- Every other baseline circuit survives the physical merger unchanged,
in each orientation, with its actual point map. -/
theorem untouched_baseline {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K → Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false)
    (j a : Fin B) (haj : a≠j) (has : a≠successor hB j) :
    (∃C : Orbit (State K B)
      (transition hK hB (flippedTurns (fun w => t w.1) (⟨0,hK⟩,j))) (2*K) (by omega),
      ∀i, C.point i=(baselineOrbit hK hB t hb a).point i) ∧
    (∃C : Orbit (State K B)
      (transition hK hB (flippedTurns (fun w => t w.1) (⟨0,hK⟩,j))) (2*K) (by omega),
      ∀i, C.point i=(reverseBaseline hK hB t hb a).point i) := by
  have hp := zero_ports hK hB t hb ht j
  constructor
  · apply away_flip hK hB (by omega) (fun w => t w.1) (⟨0,hK⟩,j)
      (baselineOrbit hK hB t hb a)
    · intro i; rw [←hp.2.2.2]; exact positive_reverse_disjoint hK hB t hb _ _ _ _
    · intro i; rw [←hp.1]; exact baseline_disjoint hK hB t hb haj _ _
    · intro i; rw [←hp.2.2.1]; exact positive_reverse_disjoint hK hB t hb _ _ _ _
    · intro i; rw [←hp.2.1]; exact baseline_disjoint hK hB t hb has _ _
  · apply away_flip hK hB (by omega) (fun w => t w.1) (⟨0,hK⟩,j)
      (reverseBaseline hK hB t hb a)
    · intro i; rw [←hp.2.2.2]; exact reverse_disjoint hK hB t hb has _ _
    · intro i; rw [←hp.1]; exact Ne.symm (positive_reverse_disjoint hK hB t hb _ _ _ _)
    · intro i; rw [←hp.2.2.1]; exact reverse_disjoint hK hB t hb haj _ _
    · intro i; rw [←hp.2.1]; exact Ne.symm (positive_reverse_disjoint hK hB t hb _ _ _ _)

private theorem close_disjoint {X : Type} {T : X→X} {M N : Nat} {hM : 0<M} {hN : 0<N}
    (C : Orbit X T M hM) (D : Orbit X T N hN) (c : Fin M) (d : Fin N)
    (hd : ∀i j, C.point i≠D.point j) :
    ∀i j, (closeAt C c).point i≠(closeAt D d).point j := by
  intro i j
  exact hd _ _

private theorem successor_ne {B : Nat} (hB : 0<B) (h2 : 2≤B) (j : Fin B) :
    successor hB j ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  change (j.val+1)%B=j.val at hv
  by_cases hj : j.val+1<B
  · rw [Nat.mod_eq_of_lt hj] at hv
    omega
  · have he : j.val+1=B := by have := j.isLt; omega
    rw [he,Nat.mod_self] at hv
    omega

theorem closeAt_image {X : Type} {T : X→X} {N : Nat} {hN : 0<N}
    (C : Orbit X T N hN) (cut : Fin N) (s : X) :
    (∃i, (closeAt C cut).point i=s) ↔ (∃i, C.point i=s) := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨k,hk⟩ := forward_surjective hN (successor hN cut) i
    exact ⟨k,by simpa only [closeAt,hk] using hi⟩

/-- The concrete four directed baseline blocks touched by row j. -/
def NeighborState {K B : Nat} (hK : 0<K) (hB : 0<B) (t : Fin K → Bool)
    (hb : BalancedTurns t) (j : Fin B) (s : State K B) : Prop :=
    (∃i, (baselineOrbit hK hB t hb j).point i=s) ∨
    (∃i, (baselineOrbit hK hB t hb (successor hB j)).point i=s) ∨
    (∃i, (reverseBaseline hK hB t hb j).point i=s) ∨
    (∃i, (reverseBaseline hK hB t hb (successor hB j)).point i=s)

/-- A physical column-zero flip really merges two neighboring baseline circuits
in BOTH orientations. Neither output orbit is an existence hypothesis. -/
theorem first_flip {K B : Nat} (hK : 0<K) (hB : 0<B) (h2 : 2≤B)
    (t : Fin K → Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) (j : Fin B) :
    ∃ C D : Orbit (State K B)
      (transition hK hB (flippedTurns (fun w => t w.1) (⟨0,hK⟩,j)))
      (2*K+2*K) (by omega), (∀i k, C.point i ≠ D.point k) ∧
      (∀s, ((∃i, C.point i=s) ∨ (∃i, D.point i=s)) ↔ NeighborState hK hB t hb j s) := by
  let p0 := CubeCycle.index hK (⟨0,hK⟩,false)
  let p1 := CubeCycle.index hK (⟨0,hK⟩,true)
  let C := closeAt (reverseBaseline hK hB t hb (successor hB j)) p1.rev
  let D := closeAt (baselineOrbit hK hB t hb j) p0
  let U := closeAt (reverseBaseline hK hB t hb j) p0.rev
  let V := closeAt (baselineOrbit hK hB t hb (successor hB j)) p1
  have hj := successor_ne hB h2 j
  have hCD : ∀i k, C.point i≠D.point k :=
    close_disjoint _ _ _ _ (fun i k => Ne.symm (positive_reverse_disjoint hK hB t hb _ _ k i))
  have hUV : ∀i k, U.point i≠V.point k :=
    close_disjoint _ _ _ _ (fun i k => Ne.symm (positive_reverse_disjoint hK hB t hb _ _ k i))
  have hCU : ∀i k, C.point i≠U.point k :=
    close_disjoint _ _ _ _ (reverse_disjoint hK hB t hb hj)
  have hCV : ∀i k, C.point i≠V.point k :=
    close_disjoint _ _ _ _ (fun i k => Ne.symm (positive_reverse_disjoint hK hB t hb _ _ k i))
  have hDU : ∀i k, D.point i≠U.point k :=
    close_disjoint _ _ _ _ (positive_reverse_disjoint hK hB t hb _ _)
  have hDV : ∀i k, D.point i≠V.point k :=
    close_disjoint _ _ _ _ (baseline_disjoint hK hB t hb (Ne.symm hj))
  have hp := zero_ports hK hB t hb ht j
  have hc : C.point (lastIndex (by omega))=(⟨0,hK⟩,j,.up) := by
    exact (closeAt_last _ _).trans hp.2.2.2
  have hd : D.point (lastIndex (by omega))=(⟨0,hK⟩,j,.down) := by
    exact (closeAt_last _ _).trans hp.1
  have hu : U.point (lastIndex (by omega))=(⟨0,hK⟩,j,.left) := by
    exact (closeAt_last _ _).trans hp.2.2.1
  have hv : V.point (lastIndex (by omega))=(⟨0,hK⟩,j,.right) := by
    exact (closeAt_last _ _).trans hp.2.1
  have he : splice (splice (transition hK hB (fun w => t w.1))
      (C.point (lastIndex (by omega))) (D.point (lastIndex (by omega))))
      (U.point (lastIndex (by omega))) (V.point (lastIndex (by omega))) =
      transition hK hB (flippedTurns (fun w => t w.1) (⟨0,hK⟩,j)) := by
    rw [hc,hd,hu,hv]
    funext s
    exact (flip_transition hK hB (fun w => t w.1) (⟨0,hK⟩,j) s).symm
  let J := doubleSplice C D U V hCD hUV hCU hCV hDU hDV
  have hdis : ∀i k, J.1.point i≠J.2.point k :=
    doubleSplice_disjoint C D U V hCD hUV hCU hCV hDU hDV
  have himage (s : State K B) :
      ((∃i, J.1.point i=s) ∨ (∃i, J.2.point i=s)) ↔ NeighborState hK hB t hb j s := by
    change ((∃i, joined C D i=s) ∨ (∃i, joined U V i=s)) ↔ _
    rw [joined_image,joined_image]
    change (((∃i, (closeAt (reverseBaseline hK hB t hb (successor hB j)) p1.rev).point i=s) ∨
      (∃i, (closeAt (baselineOrbit hK hB t hb j) p0).point i=s)) ∨
      ((∃i, (closeAt (reverseBaseline hK hB t hb j) p0.rev).point i=s) ∨
      (∃i, (closeAt (baselineOrbit hK hB t hb (successor hB j)) p1).point i=s))) ↔ _
    rw [closeAt_image,closeAt_image,closeAt_image,closeAt_image]
    change ((_) ∨ (_)) ↔ (_ ∨ _ ∨ _ ∨ _)
    constructor
    · rintro ((ha | hb') | (hc' | hd'))
      · exact Or.inr (Or.inr (Or.inr ha))
      · exact Or.inl hb'
      · exact Or.inr (Or.inr (Or.inl hc'))
      · exact Or.inr (Or.inl hd')
    · rintro (ha | hb' | hc' | hd')
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inr hb')
      · exact Or.inr (Or.inl hc')
      · exact Or.inl (Or.inl hd')
  have out := (⟨J.1,J.2,hdis,himage⟩ : ∃ C' D' : Orbit (State K B)
    (splice (splice (transition hK hB (fun w => t w.1))
      (C.point (lastIndex (by omega))) (D.point (lastIndex (by omega))))
      (U.point (lastIndex (by omega))) (V.point (lastIndex (by omega))))
    (2*K+2*K) (by omega), (∀i k, C'.point i≠D'.point k) ∧
      (∀s, ((∃i, C'.point i=s) ∨ (∃i, D'.point i=s)) ↔ NeighborState hK hB t hb j s))
  rw [he] at out
  exact out

#print axioms baselineOrbit
#print axioms reverseBaseline
#print axioms baseline_covers
#print axioms away_flip
#print axioms zero_ports
#print axioms first_flip
#print axioms untouched_baseline

end ErdePaths.AACChain
