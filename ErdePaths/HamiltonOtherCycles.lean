import ErdePaths.HamiltonCycles

namespace ErdePaths.HamiltonOtherCycles
open HamiltonData HamiltonScan HamiltonNormalize HamiltonResidual HamiltonCycles SquareLift

theorem backward_successor {N} (hN : 0<N) (a t : Fin N) :
    successor hN (backward hN a (successor hN t))=backward hN a t := by
  by_cases ht : t.val+1<N
  · have hs : successor hN t=⟨t.val+1,ht⟩ := Fin.ext (Nat.mod_eq_of_lt ht)
    rw [hs]
    exact successor_backward_step hN a ht
  · have he : t=(⟨N-1,by omega⟩ : Fin N) := by
      apply Fin.ext
      change t.val=N-1
      have := t.isLt
      omega
    have hs : successor hN t=⟨0,hN⟩ := by
      apply Fin.ext
      change (t.val+1)%N=0
      have hh : t.val+1=N := by have := t.isLt; omega
      rw [hh,Nat.mod_self]
    rw [hs,backward_zero,he,backward_last]

/-- Actual counterclockwise cyclic tour and its actual inverse clock. -/
def reverseAt {V R N hN} (C : CycleData V R N hN) (a : Fin N)
    (hsym : ∀ u v, R u v → R v u) : CycleData V R N hN where
  cycle t := C.cycle (backward hN a t)
  position v := backward hN a (C.position v)
  position_cycle t := by simp only [C.position_cycle,backward_inverse]
  cycle_position v := by rw [backward_inverse,C.cycle_position]
  adjacent t := by
    have hc := C.adjacent (backward hN a (successor hN t))
    rw [backward_successor] at hc
    exact hsym _ _ hc

theorem reverseAt_zero {V R N hN} (C : CycleData V R N hN) (a : Fin N)
    (hsym : ∀ u v, R u v → R v u) : (reverseAt C a hsym).cycle ⟨0,hN⟩=C.cycle a := by
  simp only [reverseAt,backward_zero]

theorem reverseAt_last {V R N hN} (C : CycleData V R N hN) (a : Fin N)
    (hsym : ∀ u v, R u v → R v u) :
    (reverseAt C a hsym).cycle ⟨N-1,by omega⟩=C.cycle (successor hN a) := by
  simp only [reverseAt,backward_last]

def normalizedOther {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hsym : ∀ u v, R u v → R v u) (i : Fin k) :
    CycleData V R N hN :=
  if raw cycles selected (i,false)<raw cycles selected (i,true) then
    reverseAt (cycles i.succ) (selected i.succ) hsym
  else closeSelected (cycles i.succ) (selected i.succ)

theorem normalizedOther_zero {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (hsym : ∀ u v, R u v → R v u) (i : Fin k) :
    (normalizedOther cycles selected hsym i).cycle ⟨0,hN⟩ =
      vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).lower i) := by
  change _ = vertexAt _ (sorted (raw cycles selected) (i,false))
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [normalizedOther,sorted,sortCode,ite_eq_left h,reverseAt_zero,raw_vertex]
    rfl
  · simp only [normalizedOther,sorted,sortCode,ite_eq_right h,Bool.not_false,
      closeSelected_zero,raw_vertex]
    rfl

theorem normalizedOther_last {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (hsym : ∀ u v, R u v → R v u) (i : Fin k) :
    (normalizedOther cycles selected hsym i).cycle ⟨N-1,by omega⟩ =
      vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).upper i) := by
  change _ = vertexAt _ (sorted (raw cycles selected) (i,true))
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [normalizedOther,sorted,sortCode,ite_eq_left h,reverseAt_last,raw_vertex]
    rfl
  · simp only [normalizedOther,sorted,sortCode,ite_eq_right h,Bool.not_true,
      closeSelected_last,raw_vertex]
    rfl

def sRow (s : Bool) : Nat := rowNat (.primary s)
def oRow (s : Bool) : Nat := rowNat (.primary (!s))

/-- The literal four row copies of the normalized open parent tour. -/
def K (N : Nat) (s : Bool) : List (Nat × Nat) :=
  P N 0 ++ (P N (oRow s)).reverse ++ P N 3 ++ (P N (sRow s)).reverse

theorem K_exact (N : Nat) (s : Bool) (v : Nat × Nat) :
    v ∈ K N s ↔ v.1<N ∧ v.2<4 := by
  rcases v with ⟨j,row⟩
  cases s <;> simp only [K,List.mem_append,List.mem_reverse,P_exact,sRow,oRow,rowNat,
    rowIndex,Bool.not_false,Bool.not_true]
  all_goals omega

theorem K_length (N : Nat) (s : Bool) : (K N s).length=4*N := by simp [K,P]; omega

private theorem perm_of_nodup_subset_length {V : Type} [DecidableEq V]
    (l r : List V) (hn : l.Nodup) (hs : l ⊆ r) (hl : r.length≤l.length) : l.Perm r := by
  induction l generalizing r with
  | nil => cases r with
    | nil => exact .nil
    | cons a r => simp at hl
  | cons a l ih =>
    have ha : a ∈ r := hs (by simp)
    have hn' := List.nodup_cons.mp hn
    have hsub : l ⊆ r.erase a := by
      intro b hb
      have hne : b≠a := by intro he; subst b; exact hn'.1 hb
      exact (List.mem_erase_of_ne hne).mpr (hs (List.mem_cons_of_mem a hb))
    have hlen : (r.erase a).length=r.length-1 := by rw [List.length_erase]; simp [ha]
    have hp := ih (r.erase a) hn'.2 hsub (by simp at hl; omega)
    exact (hp.cons a).trans (List.perm_cons_erase ha).symm

theorem K_nodup (N : Nat) (s : Bool) : (K N s).Nodup := by
  have hp := perm_of_nodup_subset_length (allVertices N) (K N s) (allVertices_nodup N)
    (fun v hv => (K_exact N s v).mpr ((allVertices_exact N v).mp hv))
    (by rw [K_length,allVertices_length]; exact Nat.le_refl _)
  exact hp.nodup (allVertices_nodup N)

theorem ring01 {V R N hN} (C : CycleData V R N hN) (j : Nat) (s : Bool) :
    G C (j,0) (j,oRow s) := by
  cases s <;> exact row_step C _ _ _ (by decide)

theorem ring13 {V R N hN} (C : CycleData V R N hN) (j : Nat) (s : Bool) :
    G C (j,oRow s) (j,3) := by
  cases s <;> exact row_step C _ _ _ (by decide)

theorem ring32 {V R N hN} (C : CycleData V R N hN) (j : Nat) (s : Bool) :
    G C (j,3) (j,sRow s) := by
  cases s <;> exact row_step C _ _ _ (by decide)

theorem ring20 {V R N hN} (C : CycleData V R N hN) (j : Nat) (s : Bool) :
    G C (j,sRow s) (j,0) := by
  cases s <;> exact row_step C _ _ _ (by decide)

theorem K_chain {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) : Chain (G C) (K N s) := by
  have hp0 := P_chain C 0 hsym N (Nat.le_refl N)
  have hpo := chain_reverse _ (G_symm C hsym) _ (P_chain C (oRow s) hsym N (Nat.le_refl N))
  have hp3 := P_chain C 3 hsym N (Nat.le_refl N)
  have hps := chain_reverse _ (G_symm C hsym) _ (P_chain C (sRow s) hsym N (Nat.le_refl N))
  have ha := chain_join _ _ _ hp0 hpo (N-1,0) (N-1,oRow s)
    (P_last _ _ hN) (by simp only [List.head?_reverse,P_last _ _ hN]) (ring01 C _ s)
  have hb := chain_join _ _ _ ha hp3 (0,oRow s) (0,3)
    (by simp only [List.getLast?_append,List.getLast?_reverse,P_head _ _ hN]; rfl)
    (P_head _ _ hN) (ring13 C _ s)
  exact chain_join _ _ _ hb hps (N-1,3) (N-1,sRow s)
    (by simp only [List.getLast?_append,P_last _ _ hN]; rfl)
    (by simp only [List.head?_reverse,P_last _ _ hN]) (ring32 C _ s)

theorem K_head (N : Nat) (s : Bool) (hN : 0<N) : (K N s).head?=some (0,0) := by
  simp only [K,List.head?_append,P_head _ _ hN]
  rfl

theorem K_last (N : Nat) (s : Bool) (hN : 0<N) : (K N s).getLast?=some (0,sRow s) := by
  simp only [K,List.getLast?_append,List.getLast?_reverse,P_head _ _ hN]
  rfl

def actualK {V R N hN} (C : CycleData V R N hN) (s : Bool) : List (V × Fin 4) :=
  (K N s).map (interpret C)

theorem actualK_nodup {V R N hN} (C : CycleData V R N hN) (s : Bool) :
    (actualK C s).Nodup := interpreted_nodup _ _ (K_nodup _ _) (fun _ h => (K_exact _ _ _).mp h)

theorem actualK_coverage {V R N hN} (C : CycleData V R N hN) (s : Bool) (v : V × Fin 4) :
    v ∈ actualK C s := interpreted_coverage _ _ (fun _ ha hb => (K_exact _ _ _).mpr ⟨ha,hb⟩) v

theorem actualK_length {V R N hN} (C : CycleData V R N hN) (s : Bool) :
    (actualK C s).length=4*N := by simp only [actualK,List.length_map,K_length]

theorem actualK_chain {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) : Chain (ActualGrid R) (actualK C s) :=
  chain_map (G C) (ActualGrid R) (interpret C) (fun _ _ h => h) _ (K_chain C s hsym)

theorem actualK_closure {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (a b : V × Fin 4) (ha : (actualK C s).getLast?=some a)
    (hb : (actualK C s).head?=some b) : ActualGrid R a b := by
  simp only [actualK,List.getLast?_map,K_last _ _ hN,Option.map_some,Option.some.injEq] at ha
  simp only [actualK,List.head?_map,K_head _ _ hN,Option.map_some,Option.some.injEq] at hb
  rw [←ha,←hb]
  exact ring20 C 0 s

/-- Generic genuine four-row Hamilton cycle, for any actual parent cycle. -/
noncomputable def fourRowCycle {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) : CycleData (V × Fin 4) (ActualGrid R) (4*N) (by omega) :=
  cycleFromList _ (actualK C s) (actualK_length C s) (actualK_nodup C s)
    (actualK_coverage C s) (actualK_chain C s hsym) (actualK_closure C s)

/-- The actual remaining factor Ki, uniformly in every old factor index. -/
noncomputable def otherCycle {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (hsym : ∀ u v, R u v → R v u) (i : Fin k) :
    CycleData (V × Fin 4) (ActualGrid R) (4*N) (by omega) :=
  fourRowCycle (normalizedOther cycles selected hsym i)
    (state (normalizedMatching cycles selected hn)
      ((normalizedMatching cycles selected hn).upper i)) hsym

/-- Counterclockwise normalization preserves every undirected parent edge,
with an explicit original cyclic edge position. -/
theorem reverseAt_step {V R N hN} (C : CycleData V R N hN) (a t : Fin N)
    (hsym : ∀ u v, R u v → R v u) : SameEdge
      ((reverseAt C a hsym).cycle t,(reverseAt C a hsym).cycle (successor hN t))
      (C.cycle (backward hN a (successor hN t)),
        C.cycle (successor hN (backward hN a (successor hN t)))) := by
  apply Or.inr
  simp only [reverseAt,backward_successor]

theorem normalizedOther_closing_sameEdge {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hsym : ∀ u v, R u v → R v u) (i : Fin k) : SameEdge
      ((normalizedOther cycles selected hsym i).cycle ⟨N-1,by omega⟩,
       (normalizedOther cycles selected hsym i).cycle ⟨0,hN⟩)
      ((cycles i.succ).cycle (selected i.succ),
       (cycles i.succ).cycle (successor hN (selected i.succ))) := by
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [normalizedOther,ite_eq_left h,reverseAt_zero,reverseAt_last]
    exact Or.inr rfl
  · simp only [normalizedOther,ite_eq_right h,closeSelected_zero,closeSelected_last]
    exact Or.inl rfl

def originalIndex {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (i : Fin k) (t : Fin N) : Fin N :=
  if raw cycles selected (i,false)<raw cycles selected (i,true) then
    backward hN (selected i.succ) (successor hN t)
  else forward hN (successor hN (selected i.succ)) t

/-- Exact original cyclic edge position for each normalized edge. -/
theorem normalizedOther_step {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hsym : ∀ u v, R u v → R v u) (i : Fin k) (t : Fin N) : SameEdge
      ((normalizedOther cycles selected hsym i).cycle t,
       (normalizedOther cycles selected hsym i).cycle (successor hN t))
      ((cycles i.succ).cycle (originalIndex cycles selected i t),
       (cycles i.succ).cycle (successor hN (originalIndex cycles selected i t))) := by
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [normalizedOther,originalIndex,ite_eq_left h]
    exact reverseAt_step _ _ _ hsym
  · simp only [normalizedOther,originalIndex,ite_eq_right h,closeSelected]
    exact Or.inl (rotate_step _ _ _)

theorem successor_injective {N} (hN : 0<N) : Function.Injective (successor hN) := by
  intro a b h
  simpa only [predecessor_successor] using congrArg (predecessor hN) h

theorem originalIndex_injective {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (i : Fin k) : Function.Injective (originalIndex cycles selected i) := by
  intro a b he
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [originalIndex,ite_eq_left h] at he
    exact successor_injective hN (backward_injective hN _ he)
  · simp only [originalIndex,ite_eq_right h] at he
    exact forward_injective hN _ he

theorem originalIndex_last {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (i : Fin k) : originalIndex cycles selected i ⟨N-1,by omega⟩=selected i.succ := by
  have hl : successor hN (⟨N-1,by omega⟩ : Fin N)=⟨0,hN⟩ := by
    apply Fin.ext
    change (N-1+1)%N=0
    rw [Nat.sub_add_cancel (by omega),Nat.mod_self]
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [originalIndex,ite_eq_left h,hl,backward_zero]
  · simp only [originalIndex,ite_eq_right h,forward_last,predecessor_successor]

/-- The selected original edge is deleted precisely at the closing position. -/
theorem originalIndex_selected_iff {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (i : Fin k) (t : Fin N) : originalIndex cycles selected i t=selected i.succ ↔
      t=⟨N-1,by omega⟩ := by
  rw [←originalIndex_last cycles selected i]
  constructor
  · intro he; exact originalIndex_injective cycles selected i he
  · intro h; rw [h]

theorem originalIndex_surjective {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (i : Fin k) : Function.Surjective (originalIndex cycles selected i) := by
  intro v
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · refine ⟨predecessor hN (backward hN (selected i.succ) v),?_⟩
    simp only [originalIndex,ite_eq_left h,successor_predecessor,backward_inverse]
  · refine ⟨backward hN v (successor hN (selected i.succ)),?_⟩
    simp only [originalIndex,ite_eq_right h,forward_inverse]

#print axioms normalizedOther
#print axioms K_nodup
#print axioms otherCycle
#print axioms normalizedOther_step
#print axioms originalIndex_selected_iff
end ErdePaths.HamiltonOtherCycles
