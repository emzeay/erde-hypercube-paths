import ErdePaths.HamiltonNormalize

namespace ErdePaths.HamiltonResidual
open HamiltonScan HamiltonNormalize

def rowNat (r : Row) : Nat := (rowIndex r).val

theorem rowNat_injective : Function.Injective rowNat := by
  intro a b h
  exact rowIndex_injective (Fin.ext h)

theorem rowNat_range (r : Row) : 0<rowNat r ∧ rowNat r<4 := by
  cases r with
  | top => change 0<3 ∧ 3<4; omega
  | primary b => cases b <;> simp [rowNat,rowIndex]

theorem rowNat_surjective (r : Nat) (hr : 0<r ∧ r<4) : ∃ q, rowNat q=r := by
  have h : r=1 ∨ r=2 ∨ r=3 := by omega
  rcases h with rfl | rfl | rfl
  · exact ⟨.primary false,rfl⟩
  · exact ⟨.primary true,rfl⟩
  · exact ⟨.top,rfl⟩

def W {N k} (M : Matching N k) : List (Nat × Nat) :=
  (word M (state M)).map fun v => (v.1,rowNat v.2)

def finalRow {N k} (M : Matching N k) : Nat := if state M 0 then 2 else 1

theorem W_exact {N k} (M : Matching N k) (v : Nat × Nat) :
    v ∈ W M ↔ v=(N-1,1) ∨
      (0<v.1 ∧ v.1<N-1 ∧ 0<v.2 ∧ v.2<4) ∨ v=(0,finalRow M) := by
  constructor
  · intro hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    rcases (word_exact M (state M) a).mp ha with ha | ha | ha
    · rw [ha]; exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨ha.1,ha.2,(rowNat_range a.2).1,(rowNat_range a.2).2⟩)
    · rw [ha]
      right; right
      cases hs : state M 0 <;> simp [finalRow,rowNat,rowIndex,hs]
  · intro hv
    apply List.mem_map.mpr
    rcases hv with rfl | hv | rfl
    · exact ⟨(N-1,.primary false),(word_exact M (state M) _).mpr (Or.inl rfl),rfl⟩
    · obtain ⟨r,hr⟩ := rowNat_surjective v.2 ⟨hv.2.2.1,hv.2.2.2⟩
      exact ⟨(v.1,r),(word_exact M (state M) _).mpr (Or.inr (Or.inl ⟨hv.1,hv.2.1⟩)),
        Prod.ext rfl hr⟩
    · refine ⟨(0,.primary (state M 0)),
        (word_exact M (state M) _).mpr (Or.inr (Or.inr rfl)),?_⟩
      cases hs : state M 0 <;> simp [finalRow,rowNat,rowIndex,hs]

theorem W_nodup {N k} (M : Matching N k) (hN : 2≤N) : (W M).Nodup := by
  apply List.pairwise_map.mpr
  apply (word_nodup M (state M) hN).imp
  intro a b hab he
  exact hab (Prod.ext (congrArg (fun z : Nat × Nat => z.1) he)
    (rowNat_injective (congrArg (fun z : Nat × Nat => z.2) he)))

def P (N row : Nat) : List (Nat × Nat) := (List.range N).map fun j => (j,row)

theorem P_exact (N row : Nat) (v : Nat × Nat) : v ∈ P N row ↔ v.1<N ∧ v.2=row := by
  simp only [P,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩; exact ⟨hj,rfl⟩
  · rintro ⟨hj,hr⟩; exact ⟨v.1,hj,Prod.ext rfl hr.symm⟩

theorem P_nodup (N row : Nat) : (P N row).Nodup := by
  apply List.pairwise_map.mpr
  apply List.nodup_range.imp
  intro a b hab he
  exact hab (congrArg Prod.fst he)

def tau (v : Nat × Nat) : Nat × Nat := (v.1,3-v.2)

theorem tau_involutive (v : Nat × Nat) (h : v.2≤3) : tau (tau v)=v := by
  apply Prod.ext
  · rfl
  · simp only [tau]; omega

def R0 {N k} (M : Matching N k) : List (Nat × Nat) :=
  if state M 0 then P N 0 ++ [(N-1,2),(N-1,3),(0,3),(0,1)] ++ W M
  else P N 0 ++ W M ++ [(0,3),(N-1,3),(N-1,2),(0,2)]

def R1 {N k} (M : Matching N k) : List (Nat × Nat) :=
  if state M 0 then P N 3 ++ [(N-1,1),(N-1,0),(0,0)] ++
      ((W M).reverse.map tau) ++ [(0,2)]
  else P N 3 ++ [(N-1,1),(0,1),(0,0),(N-1,0)] ++ ((W M).map tau)

theorem tauW_exact {N k} (M : Matching N k) (v : Nat × Nat) :
    v ∈ (W M).map tau ↔ v=(N-1,2) ∨
      (0<v.1 ∧ v.1<N-1 ∧ v.2<3) ∨ v=(0,3-finalRow M) := by
  constructor
  · intro hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    rcases (W_exact M a).mp ha with ha | ha | ha
    · rw [ha]; exact Or.inl rfl
    · right; left
      simp only [tau]
      omega
    · rw [ha]; right; right; rfl
  · intro hv
    apply List.mem_map.mpr
    rcases hv with rfl | hv | rfl
    · exact ⟨(N-1,1),(W_exact M _).mpr (Or.inl rfl),rfl⟩
    · refine ⟨tau v,(W_exact M _).mpr (Or.inr (Or.inl ?_)),tau_involutive v (by omega)⟩
      simp only [tau]
      omega
    · refine ⟨(0,finalRow M),(W_exact M _).mpr (Or.inr (Or.inr rfl)),rfl⟩

theorem R0_exact {N k} (M : Matching N k) (hN : 2≤N) (v : Nat × Nat) :
    v ∈ R0 M ↔ v.1<N ∧ v.2<4 := by
  rcases v with ⟨j,row⟩
  cases hs : state M 0 <;>
    simp only [R0,hs,Bool.false_eq_true,ite_true,ite_false,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,P_exact,W_exact,Prod.mk.injEq,
      finalRow] <;> try simp only [hs,ite_true,ite_false,Prod.fst,Prod.snd,Prod.mk.injEq]
  all_goals omega

theorem R1_exact {N k} (M : Matching N k) (hN : 2≤N) (v : Nat × Nat) :
    v ∈ R1 M ↔ v.1<N ∧ v.2<4 := by
  have hr : v ∈ (W M).reverse.map tau ↔ v ∈ (W M).map tau := by
    simp only [List.mem_map,List.mem_reverse]
  rcases v with ⟨j,row⟩
  cases hs : state M 0 <;>
    simp only [R1,hs,Bool.false_eq_true,ite_true,ite_false,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false,P_exact,hr,tauW_exact,Prod.mk.injEq,
      finalRow] <;> try simp only [hs,ite_true,ite_false,Prod.fst,Prod.snd,Prod.mk.injEq]
  all_goals omega

theorem W_length {N k} (M : Matching N k) (hN : 2≤N) : (W M).length=3*N-4 := by
  simp only [W,List.length_map,word_length M (state M) hN]

theorem R0_length {N k} (M : Matching N k) (hN : 2≤N) : (R0 M).length=4*N := by
  cases hs : state M 0 <;> simp [R0,hs,P,W_length M hN] <;> omega

theorem R1_length {N k} (M : Matching N k) (hN : 2≤N) : (R1 M).length=4*N := by
  cases hs : state M 0 <;> simp [R1,hs,P,W_length M hN] <;> omega

def allVertices (N : Nat) : List (Nat × Nat) :=
  (List.range N).flatMap fun j => [(j,0),(j,1),(j,2),(j,3)]

theorem allVertices_exact (N : Nat) (v : Nat × Nat) :
    v ∈ allVertices N ↔ v.1<N ∧ v.2<4 := by
  rcases v with ⟨j,r⟩
  simp only [allVertices,List.mem_flatMap,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false,Prod.mk.injEq]
  constructor
  · rintro ⟨a,ha,h⟩; rcases h with h | h | h | h <;> omega
  · intro h
    refine ⟨j,h.1,?_⟩
    omega

theorem allVertices_nodup (N : Nat) : (allVertices N).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _; simp
  · apply List.nodup_range.imp
    intro i j hij v hv w hw he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv hw
    rcases hv with rfl | rfl | rfl | rfl <;>
      rcases hw with rfl | rfl | rfl | rfl <;>
      have hh := congrArg (fun z : Nat × Nat => z.1) he <;> exact hij hh

theorem allVertices_length (N : Nat) : (allVertices N).length=4*N := by
  have hl (l : List Nat) :
      (l.flatMap fun j => [(j,0),(j,1),(j,2),(j,3)]).length=4*l.length := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]; omega
  simpa [allVertices] using hl (List.range N)

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
      apply (List.mem_erase_of_ne hne).mpr
      exact hs (List.mem_cons_of_mem a hb)
    have hlen : (r.erase a).length=r.length-1 := by rw [List.length_erase]; simp [ha]
    have hp := ih (r.erase a) hn'.2 hsub (by simp at hl; omega)
    exact (hp.cons a).trans (List.perm_cons_erase ha).symm

theorem R0_nodup {N k} (M : Matching N k) (hN : 2≤N) : (R0 M).Nodup := by
  have hp := perm_of_nodup_subset_length (allVertices N) (R0 M) (allVertices_nodup N)
    (fun v hv => (R0_exact M hN v).mpr ((allVertices_exact N v).mp hv))
    (by rw [R0_length M hN,allVertices_length]; exact Nat.le_refl _)
  exact hp.nodup (allVertices_nodup N)

theorem R1_nodup {N k} (M : Matching N k) (hN : 2≤N) : (R1 M).Nodup := by
  have hp := perm_of_nodup_subset_length (allVertices N) (R1 M) (allVertices_nodup N)
    (fun v hv => (R1_exact M hN v).mpr ((allVertices_exact N v).mp hv))
    (by rw [R1_length M hN,allVertices_length]; exact Nat.le_refl _)
  exact hp.nodup (allVertices_nodup N)

theorem chain_append {V : Type} (G : V → V → Prop) (l r : List V)
    (hl : Chain G l) (hr : Chain G r)
    (hj : ∀ a b, l.getLast?=some a → r.head?=some b → G a b) : Chain G (l++r) := by
  induction l with
  | nil => exact hr
  | cons a l ih =>
    cases l with
    | nil => cases r with
      | nil => trivial
      | cons b r => exact ⟨hj a b rfl rfl,hr⟩
    | cons b l =>
      refine ⟨hl.1,ih hl.2 ?_⟩
      intro u v hu hv
      exact hj u v (by simpa using hu) hv

def descending : Nat → List Nat
  | 0 => []
  | n+1 => (n+1)::descending n

theorem descending_eq (n : Nat) : descending n=((List.range n).map (·+1)).reverse := by
  induction n with
  | zero => rfl
  | succ n ih => simp [descending,List.range_succ,List.map_append,List.reverse_append,ih]

def scanTail {N k} (M : Matching N k) (n : Nat) : List (Nat × Row) :=
  (descending n).flatMap (block M (state M)) ++ [(0,.primary (state M 0))]

theorem scanTail_head {N k} (M : Matching N k) (n : Nat) :
    (scanTail M n).head? = some (n,.primary (state M n)) := by
  cases n with
  | zero => rfl
  | succ n => simp [scanTail,descending,block_head]

/-- The complete literal descending scan is a graph path. No global scan
adjacency property is an input: only actual parent edges and selected chords. -/
theorem word_chain {N k} (M : Matching N k) (hN : 2≤N)
    (R : Nat → Nat → Prop) (hsym : ∀ a b, R a b → R b a)
    (hselected : ∀ i, R (M.lower i) (M.upper i))
    (hsteps : ∀ j, 0<j → j<N → R j (j-1)) :
    Chain (GridAdjacent R) (word M (state M)) := by
  have ht : ∀ n, n≤N-2 → Chain (GridAdjacent R) (scanTail M n) := by
    intro n
    induction n with
    | zero => intro _; trivial
    | succ n ih =>
      intro hn
      simp only [scanTail,descending,List.flatMap_cons,List.append_assoc]
      change Chain (GridAdjacent R) (block M (state M) (n+1) ++ scanTail M n)
      apply chain_append _ _ _ (block_chain M (state M) R hsym hselected (n+1))
        (ih (by omega))
      intro a b ha hb
      rw [block_last M (n+1) (by omega)] at ha
      rw [scanTail_head] at hb
      have ha := Option.some.inj ha
      have hb := Option.some.inj hb
      rw [←ha,←hb]
      simp only [Nat.add_sub_cancel]
      exact Or.inr ⟨rfl,hsteps (n+1) (by omega) (by omega)⟩
  have hw : word M (state M) = [(N-1,.primary false)] ++ scanTail M (N-2) := by
    simp only [word,scanTail,descending_eq,middle,List.append_assoc]
  rw [hw]
  apply chain_append _ _ _ (by trivial) (ht _ (by omega))
  intro a b ha hb
  have ha := Option.some.inj ha
  rw [scanTail_head,state_initial] at hb
  have hb := Option.some.inj hb
  rw [←ha,←hb]
  exact Or.inr ⟨rfl,by simpa [Nat.sub_sub] using hsteps (N-1) (by omega) (by omega)⟩

theorem chain_map {V U : Type} (G : V → V → Prop) (H : U → U → Prop)
    (f : V → U) (h : ∀ a b, G a b → H (f a) (f b))
    (l : List V) (hl : Chain G l) : Chain H (l.map f) := by
  induction l with
  | nil => trivial
  | cons a l ih => cases l with
    | nil => trivial
    | cons b l => exact ⟨h a b hl.1,ih hl.2⟩

theorem row_adjacent_actual (a b : Row) (h : RowAdjacent a b) :
    Adjacent (n := 2) (rowIndex a) (rowIndex b) := by
  cases a with
  | top => cases b with
    | top => simp [RowAdjacent] at h
    | primary q => cases q <;> decide
  | primary p => cases b with
    | top => cases p <;> decide
    | primary q => simp [RowAdjacent] at h

def ActualGrid {V : Type} (R : V → V → Prop) (v w : V × Fin 4) : Prop :=
  (v.1=w.1 ∧ Adjacent (n := 2) v.2 w.2) ∨ (v.2=w.2 ∧ R v.1 w.1)

theorem vertexAt_eq {V R N hN} (C : HamiltonData.CycleData V R N hN)
    (j : Nat) (hj : j<N) : vertexAt C j = C.cycle ⟨j,hj⟩ := by
  unfold vertexAt
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt hj

theorem parent_coordinate_steps {V R N hN} (C : HamiltonData.CycleData V R N hN)
    (hsym : ∀ a b, R a b → R b a) (j : Nat) (hj : 0<j) (hb : j<N) :
    R (vertexAt C j) (vertexAt C (j-1)) := by
  have he := C.adjacent ⟨j-1,by omega⟩
  have hi : SquareLift.successor hN (⟨j-1,by omega⟩ : Fin N)=⟨j,hb⟩ := by
    apply Fin.ext
    simp only [SquareLift.successor]
    have hh : j-1+1=j := by omega
    rw [hh,Nat.mod_eq_of_lt hb]
  rw [hi] at he
  rw [vertexAt_eq C j hb,vertexAt_eq C (j-1) (by omega)]
  exact hsym _ _ he

noncomputable def actualWord {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N)
    (hn : (HamiltonData.endpointList cycles selected).Nodup) : List (V × Fin 4) :=
  (word (normalizedMatching cycles selected hn) (state (normalizedMatching cycles selected hn))).map
    fun v => (vertexAt (closeSelected (cycles 0) (selected 0)) v.1,rowIndex v.2)

/-- Full W adjacency on actual graph vertices and literal binary Q₂ rows. -/
theorem actualWord_chain {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N)
    (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) (hsym : ∀ a b, R a b → R b a) :
    Chain (ActualGrid R) (actualWord cycles selected hn) := by
  let C := closeSelected (cycles 0) (selected 0)
  let M := normalizedMatching cycles selected hn
  let RC : Nat → Nat → Prop := fun a b => R (vertexAt C a) (vertexAt C b)
  have hc := word_chain M hN RC (fun a b h => hsym _ _ h)
    (normalized_selected_adjacent cycles selected hn hsym)
    (parent_coordinate_steps C hsym)
  apply chain_map (GridAdjacent RC) (ActualGrid R) _ _ _ hc
  intro a b h
  rcases h with ⟨hbase,hrow⟩ | ⟨hrow,hbase⟩
  · exact Or.inl ⟨congrArg (vertexAt C) hbase,row_adjacent_actual _ _ hrow⟩
  · exact Or.inr ⟨congrArg rowIndex hrow,hbase⟩

def interpret {V R N hN} (C : HamiltonData.CycleData V R N hN)
    (v : Nat × Nat) : V × Fin 4 :=
  (vertexAt C v.1,⟨v.2%4,Nat.mod_lt _ (by omega)⟩)

theorem interpret_injective_on_box {V R N hN}
    (C : HamiltonData.CycleData V R N hN) (a b : Nat × Nat)
    (ha : a.1<N ∧ a.2<4) (hb : b.1<N ∧ b.2<4)
    (he : interpret C a=interpret C b) : a=b := by
  have hp := congrArg (fun z : V × Fin 4 => C.position z.1) he
  change C.position (vertexAt C a.1)=C.position (vertexAt C b.1) at hp
  rw [vertexAt_eq C a.1 ha.1,vertexAt_eq C b.1 hb.1,C.position_cycle,C.position_cycle] at hp
  have hbase := congrArg Fin.val hp
  have hr := congrArg (fun z : V × Fin 4 => z.2.val) he
  change a.2%4=b.2%4 at hr
  rw [Nat.mod_eq_of_lt ha.2,Nat.mod_eq_of_lt hb.2] at hr
  exact Prod.ext hbase hr

theorem interpreted_nodup {V R N hN} (C : HamiltonData.CycleData V R N hN)
    (l : List (Nat × Nat)) (hl : l.Nodup)
    (hbox : ∀ a ∈ l, a.1<N ∧ a.2<4) : (l.map (interpret C)).Nodup := by
  apply List.pairwise_map.mpr
  apply hl.imp_of_mem
  intro a b ha hb hne he
  exact hne (interpret_injective_on_box C a b (hbox a ha) (hbox b hb) he)

theorem interpreted_coverage {V R N hN} (C : HamiltonData.CycleData V R N hN)
    (l : List (Nat × Nat)) (hcover : ∀ a, a.1<N → a.2<4 → a ∈ l)
    (v : V × Fin 4) : v ∈ l.map (interpret C) := by
  apply List.mem_map.mpr
  refine ⟨((C.position v.1).val,v.2.val),hcover _ (C.position v.1).isLt v.2.isLt,?_⟩
  apply Prod.ext
  · change vertexAt C (C.position v.1).val=v.1
    rw [vertexAt_eq C _ (C.position v.1).isLt]
    exact C.cycle_position v.1
  · apply Fin.ext
    exact Nat.mod_eq_of_lt v.2.isLt

noncomputable def actualR0 {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N)
    (hn : (HamiltonData.endpointList cycles selected).Nodup) : List (V × Fin 4) :=
  (R0 (normalizedMatching cycles selected hn)).map
    (interpret (closeSelected (cycles 0) (selected 0)))

noncomputable def actualR1 {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N)
    (hn : (HamiltonData.endpointList cycles selected).Nodup) : List (V × Fin 4) :=
  (R1 (normalizedMatching cycles selected hn)).map
    (interpret (closeSelected (cycles 0) (selected 0)))

theorem actualR0_nodup {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) : (actualR0 cycles selected hn).Nodup :=
  interpreted_nodup _ _ (R0_nodup _ hN) (fun _ h => (R0_exact _ hN _).mp h)

theorem actualR1_nodup {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) : (actualR1 cycles selected hn).Nodup :=
  interpreted_nodup _ _ (R1_nodup _ hN) (fun _ h => (R1_exact _ hN _).mp h)

theorem actualR0_coverage {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) (v : V × Fin 4) : v ∈ actualR0 cycles selected hn :=
  interpreted_coverage _ _ (fun _ ha hb => (R0_exact _ hN _).mpr ⟨ha,hb⟩) v

theorem actualR1_coverage {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) (v : V × Fin 4) : v ∈ actualR1 cycles selected hn :=
  interpreted_coverage _ _ (fun _ ha hb => (R1_exact _ hN _).mpr ⟨ha,hb⟩) v

theorem actualWord_nodup {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) : (actualWord cycles selected hn).Nodup := by
  apply word_transport_nodup _ _ hN
  intro a b ha hb he
  rw [vertexAt_eq _ a ha,vertexAt_eq _ b hb] at he
  exact congrArg Fin.val (HamiltonData.cycle_injective _ he)

theorem actualR0_length {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) : (actualR0 cycles selected hn).length=4*N := by
  simp only [actualR0,List.length_map,R0_length _ hN]

theorem actualR1_length {V R k N hN}
    (cycles : Fin (k+1) → HamiltonData.CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (HamiltonData.endpointList cycles selected).Nodup)
    (hN : 2≤N) : (actualR1 cycles selected hn).length=4*N := by
  simp only [actualR1,List.length_map,R1_length _ hN]

#print axioms W_exact
#print axioms W_nodup
#print axioms R0_nodup
#print axioms R1_nodup
#print axioms word_chain
#print axioms actualWord_chain
#print axioms actualR0_nodup
#print axioms actualR1_coverage
end ErdePaths.HamiltonResidual
