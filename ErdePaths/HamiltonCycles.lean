import ErdePaths.HamiltonResidual

namespace ErdePaths.HamiltonCycles
open HamiltonScan HamiltonNormalize HamiltonResidual HamiltonData SquareLift

def G {V R N hN} (C : CycleData V R N hN) (a b : Nat × Nat) : Prop :=
  ActualGrid R (interpret C a) (interpret C b)

theorem G_symm {V R N hN} (C : CycleData V R N hN)
    (hsym : ∀ a b, R a b → R b a) (a b : Nat × Nat) : G C a b → G C b a := by
  rintro (⟨hb,hr⟩ | ⟨hr,hb⟩)
  · exact Or.inl ⟨hb.symm,adjacent_symm hr⟩
  · exact Or.inr ⟨hr.symm,hsym _ _ hb⟩

theorem P_head (N row : Nat) (hN : 0<N) : (P N row).head?=some (0,row) := by
  simp [P,List.head?_range]
  omega

theorem P_last (N row : Nat) (hN : 0<N) : (P N row).getLast?=some (N-1,row) := by
  simp [P,List.getLast?_range]
  omega

theorem W_head {N k} (M : Matching N k) : (W M).head?=some (N-1,1) := by
  simp [W,word,rowNat,rowIndex]

theorem W_last {N k} (M : Matching N k) : (W M).getLast?=some (0,finalRow M) := by
  have hw : (word M (state M)).getLast?=some (0,.primary (state M 0)) := by
    simp only [word,List.getLast?_append]
    rfl
  simp only [W,List.getLast?_map,hw,Option.map_some]
  cases hs : state M 0 <;> simp [finalRow,rowNat,rowIndex,hs]

theorem interpret_rowNat {V R N hN} (C : CycleData V R N hN) (v : Nat × Row) :
    interpret C (v.1,rowNat v.2)=(vertexAt C v.1,rowIndex v.2) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext; exact Nat.mod_eq_of_lt (rowIndex v.2).isLt

theorem W_chain {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hN : 2≤N) (hsym : ∀ a b, R a b → R b a)
    (hsel : ∀ i, R (vertexAt C (M.lower i)) (vertexAt C (M.upper i))) :
    Chain (G C) (W M) := by
  have hc := word_chain M hN (fun a b => R (vertexAt C a) (vertexAt C b))
    (fun _ _ h => hsym _ _ h) hsel (parent_coordinate_steps C hsym)
  apply chain_map _ _ _ _ _ hc
  intro a b h
  unfold G
  rw [interpret_rowNat,interpret_rowNat]
  rcases h with ⟨hb,hr⟩ | ⟨hr,hb⟩
  · exact Or.inl ⟨congrArg (vertexAt C) hb,row_adjacent_actual _ _ hr⟩
  · exact Or.inr ⟨congrArg rowIndex hr,hb⟩

theorem P_chain {V R N hN} (C : CycleData V R N hN) (row : Nat)
    (hsym : ∀ a b, R a b → R b a) (n : Nat) (hn : n≤N) : Chain (G C) (P n row) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hp : P (n+1) row = P n row ++ [(n,row)] := by simp [P,List.range_succ]
    rw [hp]
    apply chain_append _ _ _ (ih (by omega)) (by trivial)
    intro a b ha hb
    cases n with
    | zero => simp [P] at ha
    | succ n =>
      rw [P_last _ _ (by omega)] at ha
      have ha := Option.some.inj ha
      have hb := Option.some.inj hb
      rw [←ha,←hb]
      exact G_symm C hsym _ _ (Or.inr ⟨rfl,parent_coordinate_steps C hsym (n+1) (by omega) (by omega)⟩)

theorem chain_reverse {V : Type} (R : V → V → Prop) (hsym : ∀ a b, R a b → R b a)
    (l : List V) (hl : Chain R l) : Chain R l.reverse := by
  induction l with
  | nil => trivial
  | cons a l ih => cases l with
    | nil => trivial
    | cons b l =>
      rw [List.reverse_cons]
      apply chain_append _ _ _ (ih hl.2) (by trivial)
      intro u v hu hv
      simp only [List.getLast?_reverse,List.head?_cons,Option.some.injEq] at hu
      have hv := Option.some.inj hv
      rw [←hu,←hv]
      exact hsym _ _ hl.1

def flip4 (r : Fin 4) : Fin 4 := ⟨3-r.val,by omega⟩

theorem flip4_adjacent (a b : Fin 4) : Adjacent (n := 2) a b → Adjacent (n := 2) (flip4 a) (flip4 b) := by
  have cases4 (r : Fin 4) : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by
    have hr := r.isLt
    have hh : r.val=0 ∨ r.val=1 ∨ r.val=2 ∨ r.val=3 := by omega
    rcases hh with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases cases4 a with rfl | rfl | rfl | rfl <;>
    rcases cases4 b with rfl | rfl | rfl | rfl <;> decide

theorem interpret_tau {V R N hN} (C : CycleData V R N hN) (v : Nat × Nat) (hv : v.2<4) :
    interpret C (tau v)=((interpret C v).1,flip4 (interpret C v).2) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (3-v.2)%4=3-(v.2%4)
    rw [Nat.mod_eq_of_lt hv,Nat.mod_eq_of_lt (by omega)]

theorem G_tau {V R N hN} (C : CycleData V R N hN) (a b : Nat × Nat)
    (ha : a.2<4) (hb : b.2<4) (h : G C a b) : G C (tau a) (tau b) := by
  unfold G at *
  rw [interpret_tau C a ha,interpret_tau C b hb]
  rcases h with ⟨hbase,hrow⟩ | ⟨hrow,hbase⟩
  · exact Or.inl ⟨hbase,flip4_adjacent _ _ hrow⟩
  · exact Or.inr ⟨congrArg flip4 hrow,hbase⟩

theorem chain_map_of_mem {V U : Type} (R : V → V → Prop) (S : U → U → Prop)
    (f : V → U) (l : List V) (hl : Chain R l)
    (h : ∀ a ∈ l, ∀ b ∈ l, R a b → S (f a) (f b)) : Chain S (l.map f) := by
  induction l with
  | nil => trivial
  | cons a l ih => cases l with
    | nil => trivial
    | cons b l =>
      refine ⟨h a (by simp) b (by simp) hl.1,ih hl.2 ?_⟩
      intro u hu v hv hh
      exact h u (List.mem_cons_of_mem a hu) v (List.mem_cons_of_mem a hv) hh

theorem chain_join {V : Type} (R : V → V → Prop) (l r : List V)
    (hl : Chain R l) (hr : Chain R r) (a b : V)
    (ha : l.getLast?=some a) (hb : r.head?=some b) (hab : R a b) : Chain R (l++r) := by
  apply chain_append _ _ _ hl hr
  intro u v hu hv
  rw [ha] at hu
  rw [hb] at hv
  rw [←Option.some.inj hu,←Option.some.inj hv]
  exact hab

theorem row_step {V R N hN} (C : CycleData V R N hN) (j a b : Nat)
    (h : Adjacent (n := 2) (⟨a%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)
      ⟨b%4,Nat.mod_lt _ (by decide)⟩) : G C (j,a) (j,b) := Or.inl ⟨rfl,h⟩

theorem closing_step {V R N hN} (C : CycleData V R N hN) (row : Nat) :
    G C (N-1,row) (0,row) := by
  apply Or.inr
  refine ⟨rfl,?_⟩
  change R (vertexAt C (N-1)) (vertexAt C 0)
  rw [vertexAt_eq C _ (by omega),vertexAt_eq C _ hN]
  have hi : successor hN (⟨N-1,by omega⟩ : Fin N)=⟨0,hN⟩ := by
    apply Fin.ext
    change (N-1+1)%N=0
    rw [Nat.sub_add_cancel (by omega),Nat.mod_self]
  simpa only [hi] using C.adjacent ⟨N-1,by omega⟩

theorem W_row_bound {N k} (M : Matching N k) (v : Nat × Nat) (hv : v ∈ W M) : v.2<4 := by
  rcases (W_exact M v).mp hv with hv | hv | hv
  · rw [hv]; omega
  · exact hv.2.2.2
  · rw [hv]; cases hs : state M 0 <;> simp [finalRow,hs]

theorem tauW_chain {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hc : Chain (G C) (W M)) : Chain (G C) ((W M).map tau) :=
  chain_map_of_mem _ _ _ _ hc (fun a ha b hb h => G_tau C a b (W_row_bound M a ha) (W_row_bound M b hb) h)

theorem tauRevW_chain {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hsym : ∀ a b, R a b → R b a) (hc : Chain (G C) (W M)) :
    Chain (G C) ((W M).reverse.map tau) :=
  chain_map_of_mem _ _ _ _ (chain_reverse _ (G_symm C hsym) _ hc)
    (fun a ha b hb h => G_tau C a b (W_row_bound M a (List.mem_reverse.mp ha))
      (W_row_bound M b (List.mem_reverse.mp hb)) h)

theorem R0_chain {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hN : 2≤N) (hsym : ∀ a b, R a b → R b a)
    (hsel : ∀ i, R (vertexAt C (M.lower i)) (vertexAt C (M.upper i))) :
    Chain (G C) (R0 M) := by
  have hp := P_chain C 0 hsym N (by omega)
  have hw := W_chain C M hN hsym hsel
  cases hs : state M 0
  · simp only [R0,hs,Bool.false_eq_true,ite_false]
    have hh := chain_join _ _ _ hp hw (N-1,0) (N-1,1)
      (P_last _ _ (by omega)) (W_head M) (row_step C _ _ _ (by decide))
    have hb : Chain (G C) [(0,3),(N-1,3),(N-1,2),(0,2)] :=
      ⟨G_symm C hsym _ _ (closing_step C 3),row_step C _ _ _ (by decide),closing_step C 2,trivial⟩
    apply chain_join _ _ _ hh hb (0,1) (0,3)
      (by simp only [List.getLast?_append,W_last,finalRow,hs,Bool.false_eq_true,ite_false]; rfl)
      rfl (row_step C _ _ _ (by decide))
  · simp only [R0,hs,ite_true]
    have hb : Chain (G C) [(N-1,2),(N-1,3),(0,3),(0,1)] :=
      ⟨row_step C _ _ _ (by decide),closing_step C 3,row_step C _ _ _ (by decide),trivial⟩
    have hh := chain_join _ _ _ hp hb (N-1,0) (N-1,2)
      (P_last _ _ (by omega)) rfl (row_step C _ _ _ (by decide))
    apply chain_join _ _ _ hh hw (0,1) (N-1,1)
      (by simp only [List.getLast?_append]; rfl) (W_head M)
      (G_symm C hsym _ _ (closing_step C 1))

theorem R1_chain {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hN : 2≤N) (hsym : ∀ a b, R a b → R b a)
    (hsel : ∀ i, R (vertexAt C (M.lower i)) (vertexAt C (M.upper i))) :
    Chain (G C) (R1 M) := by
  have hp := P_chain C 3 hsym N (by omega)
  have hw := W_chain C M hN hsym hsel
  cases hs : state M 0
  · simp only [R1,hs,Bool.false_eq_true,ite_false]
    have hb : Chain (G C) [(N-1,1),(0,1),(0,0),(N-1,0)] :=
      ⟨closing_step C 1,row_step C _ _ _ (by decide),G_symm C hsym _ _ (closing_step C 0),trivial⟩
    have hh := chain_join _ _ _ hp hb (N-1,3) (N-1,1)
      (P_last _ _ (by omega)) rfl (row_step C _ _ _ (by decide))
    apply chain_join _ _ _ hh (tauW_chain C M hw) (N-1,0) (N-1,2)
      (by simp only [List.getLast?_append]; rfl)
      (by simp only [List.head?_map,W_head]; rfl) (row_step C _ _ _ (by decide))
  · simp only [R1,hs,ite_true]
    have hb : Chain (G C) [(N-1,1),(N-1,0),(0,0)] :=
      ⟨row_step C _ _ _ (by decide),closing_step C 0,trivial⟩
    have hh := chain_join _ _ _ hp hb (N-1,3) (N-1,1)
      (P_last _ _ (by omega)) rfl (row_step C _ _ _ (by decide))
    have hq := tauRevW_chain C M hsym hw
    have hjoined := chain_join _ _ _ hh hq (0,0) (0,1)
      (by simp only [List.getLast?_append]; rfl)
      (by simp only [List.head?_map,List.head?_reverse,W_last,finalRow,hs,ite_true]; rfl)
      (row_step C _ _ _ (by decide))
    apply chain_join _ _ _ hjoined (by trivial) (N-1,2) (0,2)
      (by simp only [List.getLast?_append,List.getLast?_map,List.getLast?_reverse,W_head]; rfl)
      rfl (closing_step C 2)

theorem R0_head {N k} (M : Matching N k) (hN : 0<N) : (R0 M).head?=some (0,0) := by
  cases hs : state M 0 <;> simp only [R0,hs,Bool.false_eq_true,ite_true,ite_false,List.head?_append,P_head _ _ hN]
  all_goals rfl

theorem R1_head {N k} (M : Matching N k) (hN : 0<N) : (R1 M).head?=some (0,3) := by
  cases hs : state M 0 <;> simp only [R1,hs,Bool.false_eq_true,ite_true,ite_false,List.head?_append,P_head _ _ hN]
  all_goals rfl

theorem R0_last {N k} (M : Matching N k) : (R0 M).getLast?=some (0,2) := by
  cases hs : state M 0 <;> simp only [R0,hs,Bool.false_eq_true,ite_true,ite_false,List.getLast?_append,W_last,finalRow]
  all_goals try simp only [hs,ite_true]
  all_goals rfl

theorem R1_last {N k} (M : Matching N k) : (R1 M).getLast?=some (0,2) := by
  cases hs : state M 0 <;> simp only [R1,hs,Bool.false_eq_true,ite_true,ite_false,List.getLast?_append,
    List.getLast?_map,W_last,finalRow]
  all_goals try simp only [hs,ite_true,Bool.false_eq_true,ite_false]
  all_goals rfl

theorem R0_closure {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hN : 0<N) (a b : Nat × Nat) (ha : (R0 M).getLast?=some a)
    (hb : (R0 M).head?=some b) : G C a b := by
  rw [R0_last] at ha
  rw [R0_head M hN] at hb
  rw [←Option.some.inj ha,←Option.some.inj hb]
  exact row_step C _ _ _ (by decide)

theorem R1_closure {V R N k hN} (C : CycleData V R N hN) (M : Matching N k)
    (hN : 0<N) (a b : Nat × Nat) (ha : (R1 M).getLast?=some a)
    (hb : (R1 M).head?=some b) : G C a b := by
  rw [R1_last] at ha
  rw [R1_head M hN] at hb
  rw [←Option.some.inj ha,←Option.some.inj hb]
  exact row_step C _ _ _ (by decide)

theorem chain_getElem {V : Type} (R : V → V → Prop) (l : List V) (hc : Chain R l)
    (i : Nat) (hi : i+1<l.length) : R l[i] l[i+1] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih => cases l with
    | nil => simp at hi
    | cons b l =>
      cases i with
      | zero => exact hc.1
      | succ i => exact ih hc.2 i (by simpa using hi)

theorem actualR0_chain {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀ a b, R a b → R b a) : Chain (ActualGrid R) (actualR0 cycles selected hn) :=
  chain_map (G (closeSelected (cycles 0) (selected 0))) (ActualGrid R)
    (interpret (closeSelected (cycles 0) (selected 0))) (fun _ _ h => h) _
    (R0_chain _ _ hN hsym (normalized_selected_adjacent cycles selected hn hsym))

theorem actualR1_chain {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀ a b, R a b → R b a) : Chain (ActualGrid R) (actualR1 cycles selected hn) :=
  chain_map (G (closeSelected (cycles 0) (selected 0))) (ActualGrid R)
    (interpret (closeSelected (cycles 0) (selected 0))) (fun _ _ h => h) _
    (R1_chain _ _ hN hsym (normalized_selected_adjacent cycles selected hn hsym))

theorem actualR0_closure {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (a b : V × Fin 4)
    (ha : (actualR0 cycles selected hn).getLast?=some a)
    (hb : (actualR0 cycles selected hn).head?=some b) : ActualGrid R a b := by
  simp only [actualR0,List.getLast?_map,R0_last,Option.map_some,Option.some.injEq] at ha
  simp only [actualR0,List.head?_map,R0_head _ hN,Option.map_some,Option.some.injEq] at hb
  rw [←ha,←hb]
  exact row_step (closeSelected (cycles 0) (selected 0)) 0 2 0 (by decide)

theorem actualR1_closure {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (a b : V × Fin 4)
    (ha : (actualR1 cycles selected hn).getLast?=some a)
    (hb : (actualR1 cycles selected hn).head?=some b) : ActualGrid R a b := by
  simp only [actualR1,List.getLast?_map,R1_last,Option.map_some,Option.some.injEq] at ha
  simp only [actualR1,List.head?_map,R1_head _ hN,Option.map_some,Option.some.injEq] at hb
  rw [←ha,←hb]
  exact row_step (closeSelected (cycles 0) (selected 0)) 0 2 3 (by decide)

/-- A faithful cyclic bijection constructed from the actual spanning list.
Its inverse is selected from actual list positions, not an assumed clock. -/
noncomputable def cycleFromList {V : Type} {R : V → V → Prop} {L : Nat}
    (hL : 0<L) (l : List V) (hlength : l.length=L) (hn : l.Nodup)
    (hcover : ∀ v, v ∈ l) (hc : Chain R l)
    (hclose : ∀ a b, l.getLast?=some a → l.head?=some b → R a b) : CycleData V R L hL := by
  classical
  let f : Fin L → V := fun i => l[i.val]'(by have := i.isLt; omega)
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (hn.eq_of_getElem_eq (by have := i.isLt; omega)
      (by have := j.isLt; omega) h)
  have hs : ∀ v, ∃ i : Fin L, f i=v := by
    intro v
    obtain ⟨j,hj,hv⟩ := List.mem_iff_getElem.mp (hcover v)
    exact ⟨⟨j,by omega⟩,hv⟩
  let inv : V → Fin L := fun v => (hs v).choose
  have hinv : ∀ v, f (inv v)=v := fun v => (hs v).choose_spec
  refine {
    cycle := f
    position := inv
    position_cycle := fun i => hf (hinv (f i))
    cycle_position := hinv
    adjacent := ?_ }
  intro i
  by_cases hi : i.val+1<L
  · have hsucc : successor hL i=⟨i.val+1,hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    rw [hsucc]
    exact chain_getElem R l hc i.val (by omega)
  · have hlast : i.val=L-1 := by have := i.isLt; omega
    have hsucc : successor hL i=⟨0,hL⟩ := by
      apply Fin.ext
      change (i.val+1)%L=0
      have hh : i.val+1=L := by have := i.isLt; omega
      rw [hh,Nat.mod_self]
    rw [hsucc]
    apply hclose (f i) (f ⟨0,hL⟩)
    · rw [List.getLast?_eq_getElem?]
      have hj : l.length-1=i.val := by omega
      rw [hj]
      exact List.getElem?_eq_getElem (by have := i.isLt; omega)
    · rw [List.head?_eq_getElem?]
      exact List.getElem?_eq_getElem (by omega)

noncomputable def residualCycle0 {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀ a b, R a b → R b a) : CycleData (V × Fin 4) (ActualGrid R) (4*N) (by omega) :=
  cycleFromList _ (actualR0 cycles selected hn) (actualR0_length cycles selected hn hN)
    (actualR0_nodup cycles selected hn hN) (actualR0_coverage cycles selected hn hN)
    (actualR0_chain cycles selected hn hN hsym) (actualR0_closure cycles selected hn)

noncomputable def residualCycle1 {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀ a b, R a b → R b a) : CycleData (V × Fin 4) (ActualGrid R) (4*N) (by omega) :=
  cycleFromList _ (actualR1 cycles selected hn) (actualR1_length cycles selected hn hN)
    (actualR1_nodup cycles selected hn hN) (actualR1_coverage cycles selected hn hN)
    (actualR1_chain cycles selected hn hN hsym) (actualR1_closure cycles selected hn)

#print axioms R0_chain
#print axioms R1_chain
#print axioms residualCycle0
#print axioms residualCycle1

#print axioms W_chain
end ErdePaths.HamiltonCycles
