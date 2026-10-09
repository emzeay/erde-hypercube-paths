import ErdePaths.AACInduction
import ErdePaths.AACEdge

namespace ErdePaths.AACOwnership
open SquareLift AACTransition AACMerge AACChain AACInduction AACEdge

/-- Pairing at an unmodified grid exchanges the two literal baseline traversals. -/
theorem baseline_pair_image {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (rev : Bool) (a : Fin B) (s : State K B) :
    InOrbit (baselineClock hK hB t hb rev a) s →
      InOrbit (baselineClock hK hB t hb (!rev) a) (atPair (fun w => t w.1) s) := by
  rintro ⟨i,hi⟩
  cases rev
  · change (baselineOrbit hK hB t hb a).point i=s at hi
    refine ⟨i.rev,?_⟩
    change atPair (fun w => t w.1) ((baselineOrbit hK hB t hb a).point i.rev.rev)=_
    rw [Fin.rev_rev,hi]
  · refine ⟨i.rev,?_⟩
    change (baselineOrbit hK hB t hb a).point i.rev=atPair (fun w => t w.1) s
    rw [←hi]
    exact (atPair_involutive (fun w => t w.1) _).symm

private theorem orientation_not (side : Bool) (n : Nat) :
    orientation (!side) n=!(orientation side n) := by
  by_cases he : n%2=0 <;> simp [orientation,he]

private theorem orientation_next (side : Bool) (n : Nat) :
    orientation (!side) (n+1)=orientation side n ∧
      orientation (!side) n=orientation side (n+1) := by
  have hm := Nat.mod_lt n (by omega : 0<2)
  by_cases he : n%2=0
  · have hn : (n+1)%2=1 := by omega
    simp [orientation,he,hn]
  · have hn : n%2=1 := by omega
    have hn' : (n+1)%2=0 := by omega
    simp [orientation,hn,hn']

/-- Membership of a canonical baseline state has exactly the prescribed
label/orientation, using the global directed-state injection. -/
theorem prefix_clock {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (side rev : Bool) (k : Nat)
    (a : Fin B) (ha : a.val≤k) (i : Fin (2*K)) :
    Prefix hK hB t hb side k ((baselineClock hK hB t hb rev a).point i) ↔
      orientation side a.val=rev := by
  constructor
  · rintro ⟨b,hb',j,hj⟩
    by_cases he : b=a
    · subst b
      by_cases hr : orientation side a.val=rev
      · exact hr
      · exact False.elim (clock_disjoint hK hB t hb (Or.inr hr) j i hj)
    · exact False.elim (clock_disjoint hK hB t hb (Or.inl he) j i hj)
  · intro he
    refine ⟨a,ha,i,?_⟩
    rw [he]

private theorem zero_prefix_ports {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false)
    (side : Bool) (j : Fin B) :
    (Prefix hK hB t hb side (B-1) (⟨0,hK⟩,j,.down) ↔ orientation side j.val=false) ∧
    (Prefix hK hB t hb side (B-1) (⟨0,hK⟩,j,.left) ↔ orientation side j.val=true) ∧
    (Prefix hK hB t hb side (B-1) (⟨0,hK⟩,j,.right) ↔ orientation side (successor hB j).val=false) ∧
    (Prefix hK hB t hb side (B-1) (⟨0,hK⟩,j,.up) ↔ orientation side (successor hB j).val=true) := by
  have hp := zero_ports hK hB t hb ht j
  constructor
  · rw [←hp.1]
    exact prefix_clock hK hB t hb side false _ j (by have := j.isLt; omega) _
  constructor
  · rw [←hp.2.2.1]
    exact prefix_clock hK hB t hb side true _ j (by have := j.isLt; omega) _
  constructor
  · rw [←hp.2.1]
    exact prefix_clock hK hB t hb side false _ (successor hB j) (by have := (successor hB j).isLt; omega) _
  · rw [←hp.2.2.2]
    exact prefix_clock hK hB t hb side true _ (successor hB j) (by have := (successor hB j).isLt; omega) _

/-- The actual final turn pairing exchanges the two alternating Prefix images. -/
theorem final_pair_side {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false)
    (side : Bool) (s : State K B) (hs : Prefix hK hB t hb side (B-1) s) :
    Prefix hK hB t hb (!side) (B-1) (atPair (turnsAfter hK t (B-1)) s) := by
  by_cases hg : s.1=⟨0,hK⟩ ∧ s.2.1.val<B-1
  · rcases s with ⟨i,j,p⟩
    simp only at hg
    obtain ⟨hi,hj⟩ := hg
    subst i
    have hj' : j.val+1<B := by omega
    have hsucc : (successor hB j).val=j.val+1 := Nat.mod_eq_of_lt hj'
    have hp := zero_prefix_ports hK hB t hb ht side j
    have hq := zero_prefix_ports hK hB t hb ht (!side) j
    have ho := orientation_next side j.val
    rw [←hsucc] at ho
    have turn : turnsAfter hK t (B-1) (⟨0,hK⟩,j)=true := by simp [turnsAfter,hj,ht]
    cases p
    · change Prefix hK hB t hb (!side) (B-1) (⟨0,hK⟩,j,pair (turnsAfter hK t (B-1) (⟨0,hK⟩,j)) .up)
      rw [turn]
      apply hq.2.1.mpr
      rw [ho.2]
      exact hp.2.2.2.mp hs
    · change Prefix hK hB t hb (!side) (B-1) (⟨0,hK⟩,j,pair (turnsAfter hK t (B-1) (⟨0,hK⟩,j)) .right)
      rw [turn]
      apply hq.1.mpr
      rw [ho.2]
      exact hp.2.2.1.mp hs
    · change Prefix hK hB t hb (!side) (B-1) (⟨0,hK⟩,j,pair (turnsAfter hK t (B-1) (⟨0,hK⟩,j)) .down)
      rw [turn]
      apply hq.2.2.1.mpr
      rw [ho.1]
      exact hp.1.mp hs
    · change Prefix hK hB t hb (!side) (B-1) (⟨0,hK⟩,j,pair (turnsAfter hK t (B-1) (⟨0,hK⟩,j)) .left)
      rw [turn]
      apply hq.2.2.2.mpr
      rw [ho.1]
      exact hp.2.1.mp hs
  · have he : atPair (turnsAfter hK t (B-1)) s=atPair (fun w => t w.1) s := by
      simp only [atPair,turnsAfter,hg,↓reduceIte]
    rw [he]
    obtain ⟨a,ha,hi⟩ := hs
    refine ⟨a,ha,?_⟩
    rw [orientation_not]
    exact baseline_pair_image hK hB t hb _ a s hi


theorem incoming_step {K B : Nat} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B→Bool) (s : State K B) :
    SameEdge (coarseDecode hK hB (incoming hK hB (transition hK hB turns s)))
      (stateVertex s,stateVertex (transition hK hB turns s)) := by
  have hx (u : State K B) : SameEdge (coarseDecode hK hB (incoming hK hB (cross hK hB u)))
      (stateVertex u,stateVertex (cross hK hB u)) := by
    rw [cross_incoming]
    rcases u with ⟨i,j,p⟩
    cases p
    · exact Or.inl rfl
    · exact Or.inl rfl
    · apply Or.inr
      simp [incoming,coarseDecode,stateVertex,cross,successor_predecessor]
    · apply Or.inr
      simp [incoming,coarseDecode,stateVertex,cross,successor_predecessor]
  exact hx (atPair turns s)

/-- A final constructed AAC clock owns every actual undirected coarse LABEL
exactly once. Parallel cyclic labels remain distinguished. -/
theorem coarse_euler {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
      (Function.Injective (fun i => incoming hK hB (C.point i)) ∧
        Function.Surjective (fun i => incoming hK hB (C.point i))) ∧
      (∀i, SameEdge (coarseDecode hK hB (incoming hK hB (C.point (successor (Nat.mul_pos hB (by omega)) i))))
        (stateVertex (C.point i),stateVertex (C.point (successor (Nat.mul_pos hB (by omega)) i)))) := by
  obtain ⟨G,gi,gd,gc⟩ := full_chain hK hB t hb ht
  let turns : Grid K B→Bool := turnsAfter hK t (B-1)
  have tp (side : Bool) (s : State K B) (hs : Prefix hK hB t hb side (B-1) s) :
      Prefix hK hB t hb side (B-1) (transition hK hB turns s) := by
    obtain ⟨i,hi⟩ := (gi side s).mpr hs
    apply (gi side _).mp
    exact ⟨successor (Nat.mul_pos hB (by omega)) i,by rw [←(G side).next i,hi]⟩
  have xp (side : Bool) (s : State K B) (hs : Prefix hK hB t hb side (B-1) s) :
      Prefix hK hB t hb (!side) (B-1) (cross hK hB s) := by
    have hpair := final_pair_side hK hB t hb ht side s hs
    have htrans := tp (!side) _ hpair
    simpa only [turns,transition,atPair_involutive] using htrans
  have hinj : Function.Injective (fun i => incoming hK hB ((G false).point i)) := by
    intro i j he
    rcases incoming_fiber hK hB _ _ he with hs | hs
    · exact (G false).injective hs
    · have hp := (gi false ((G false).point j)).mp ⟨j,rfl⟩
      have hq := xp false _ hp
      rw [←hs] at hq
      exact False.elim (prefix_disjoint hK hB t hb (B-1) _
        ((gi false ((G false).point i)).mp ⟨i,rfl⟩) hq)
  have hsur : Function.Surjective (fun i => incoming hK hB ((G false).point i)) := by
    intro e
    obtain ⟨s,hs⟩ := incoming_surjective hK hB e
    rcases gc s with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨i,by change incoming hK hB ((G false).point i)=e; rw [hi,hs]⟩
    · have hp := (gi true s).mp ⟨j,hj⟩
      have hq := xp true s hp
      obtain ⟨i,hi⟩ := (gi false _).mpr hq
      exact ⟨i,by change incoming hK hB ((G false).point i)=e; rw [hi,cross_incoming,hs]⟩
  refine ⟨G false,⟨hinj,hsur⟩,?_⟩
  intro i
  rw [←(G false).next i]
  exact incoming_step hK hB turns _

/-- The owned edge labels can be indexed at the outgoing step itself. -/
theorem coarse_euler_steps {K B : Nat} (hK : 0<K) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
      (Function.Injective (fun i => incoming hK hB (C.point (successor (Nat.mul_pos hB (by omega)) i))) ∧
       Function.Surjective (fun i => incoming hK hB (C.point (successor (Nat.mul_pos hB (by omega)) i)))) ∧
      (∀i, SameEdge (coarseDecode hK hB (incoming hK hB (C.point (successor (Nat.mul_pos hB (by omega)) i))))
        (stateVertex (C.point i),stateVertex (C.point (successor (Nat.mul_pos hB (by omega)) i)))) := by
  obtain ⟨C,⟨hinj,hsur⟩,hstep⟩ := coarse_euler hK hB t hb ht
  refine ⟨C,⟨?_,?_⟩,hstep⟩
  · intro i j he
    have hh := hinj he
    have hp := congrArg (predecessor (Nat.mul_pos hB (by omega))) hh
    simpa only [predecessor_successor] using hp
  · intro e
    obtain ⟨i,hi⟩ := hsur e
    refine ⟨predecessor (Nat.mul_pos hB (by omega)) i,?_⟩
    change incoming hK hB (C.point (successor (Nat.mul_pos hB (by omega))
      (predecessor (Nat.mul_pos hB (by omega)) i)))=e
    rw [successor_predecessor]
    exact hi

/-- Literal fine base edges have a unique coarse clock position and subdivision
offset. This is an ownership bridge, not yet an ordered fine Euler traversal. -/
theorem fine_base_owner {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (states : Fin N→State K B)
    (hinj : Function.Injective (fun n => incoming hK hB (states n)))
    (hsur : Function.Surjective (fun n => incoming hK hB (states n)))
    (x : Fin (K*A)) (j : Fin B) :
    ∃p : Fin N × Fin A, (∃i : Fin K,
      incoming hK hB (states p.1)=Sum.inl (i,j) ∧ AnchoredEmbedding.positionEncode i p.2=x) ∧
      (∀q : Fin N × Fin A, (∃i : Fin K, incoming hK hB (states q.1)=Sum.inl (i,j) ∧
        AnchoredEmbedding.positionEncode i q.2=x) → q=p) := by
  let d := AnchoredEmbedding.positionDecode hA x
  obtain ⟨n,hn⟩ := hsur (Sum.inl (d.1,j))
  change incoming hK hB (states n)=Sum.inl (d.1,j) at hn
  refine ⟨(n,d.2),⟨d.1,hn,AnchoredEmbedding.positionEncode_decode hA x⟩,?_⟩
  rintro ⟨m,a⟩ ⟨i,hi,hx⟩
  have he : (i,a)=d := by
    have hh := congrArg (AnchoredEmbedding.positionDecode hA) hx
    simpa only [AnchoredEmbedding.positionDecode_encode] using hh
  have hei : i=d.1 := congrArg Prod.fst he
  have hea : a=d.2 := congrArg Prod.snd he
  have hmn : m=n := by
    apply hinj
    change incoming hK hB (states m)=incoming hK hB (states n)
    rw [hi,hn,hei]
  exact Prod.ext hmn hea

/-- Unsubdivided second-axis edges retain the exact coarse clock owner. -/
theorem fine_second_owner {K B N : Nat} (hK : 0<K) (hB : 0<B)
    (states : Fin N→State K B)
    (hinj : Function.Injective (fun n => incoming hK hB (states n)))
    (hsur : Function.Surjective (fun n => incoming hK hB (states n)))
    (i : Fin K) (j : Fin B) :
    ∃n : Fin N, incoming hK hB (states n)=Sum.inr (i,j) ∧
      (∀m : Fin N, incoming hK hB (states m)=Sum.inr (i,j) → m=n) := by
  obtain ⟨n,hn⟩ := hsur (Sum.inr (i,j))
  exact ⟨n,hn,fun m hm => hinj (hm.trans hn.symm)⟩

#print axioms final_pair_side
#print axioms coarse_euler
#print axioms coarse_euler_steps
#print axioms fine_base_owner
#print axioms fine_second_owner

end ErdePaths.AACOwnership
