import ErdePaths.HamiltonOtherCycles

namespace ErdePaths.HamiltonLedger
open HamiltonData HamiltonScan HamiltonNormalize HamiltonResidual HamiltonCycles HamiltonOtherCycles SquareLift

theorem successor_val {N} (hN : 0<N) (t : Fin N) :
    (successor hN t).val = if t.val+1<N then t.val+1 else 0 := by
  change (t.val+1)%N = _
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · have he : t.val+1=N := by have := t.isLt; omega
    rw [he,Nat.mod_self]

theorem no_successor_two_cycle {N} (hN : 0<N) (h3 : 3≤N) (t : Fin N) :
    successor hN (successor hN t) ≠ t := by
  intro h
  have hv := congrArg Fin.val h
  rw [successor_val,successor_val] at hv
  split at hv <;> split at hv <;> have := t.isLt <;> omega

/-- A genuine Hamilton cycle of length at least three owns an undirected
edge at only one cyclic position, including the closing position. -/
theorem cyclic_position_unique {V R N hN} (C : CycleData V R N hN) (h3 : 3≤N)
    (s t : Fin N) (h : SameEdge (C.cycle s,C.cycle (successor hN s))
      (C.cycle t,C.cycle (successor hN t))) : s=t := by
  rcases h with h | h
  · exact cycle_injective C (congrArg Prod.fst h)
  · have hs := cycle_injective C (congrArg Prod.fst h)
    have ht := cycle_injective C (congrArg Prod.snd h)
    have he : successor hN (successor hN t)=t := by rw [←hs,ht]
    exact False.elim (no_successor_two_cycle hN h3 t he)

def Uses (l : List (Nat × Row)) (e : (Nat × Row) × (Nat × Row)) : Prop :=
  ∃ f, f ∈ steps l ∧ SameEdge f e

inductive Label (k : Nat) where
  | chord : Fin k → Row → Label k
  | vertical : Nat → Bool → Label k
  deriving DecidableEq

def labelEdge {N k} (M : Matching N k) : Label k → (Nat × Row) × (Nat × Row)
  | .chord i r => ((M.lower i,r),(M.upper i,r))
  | .vertical j s => ((j,.primary s),(j,.top))

/-- Canonical local allocations, independent of the incoming lower state. -/
def labels {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat) : List (Label k) :=
  match M.kind j with
  | .ordinary => [.vertical j (s j),.vertical j (!(s j))]
  | .upper _ => []
  | .lower i => [.vertical j (s (M.upper i)),.chord i .top,
      .vertical (M.upper i) (!(s (M.upper i))),.chord i (.primary (!(s (M.upper i))))]

theorem sameEdge_symm {V : Type} (e f : V × V) : SameEdge e f → SameEdge f e := by
  rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr (by cases e; cases f; simp only [Prod.mk.injEq] at h ⊢; exact ⟨h.2.symm,h.1.symm⟩)

theorem sameEdge_trans {V : Type} (e f g : V × V) : SameEdge e f → SameEdge f g → SameEdge e g := by
  cases e with
  | mk a b => cases f with
    | mk c d => cases g with
      | mk u v => simp only [SameEdge,Prod.mk.injEq]; grind

theorem Uses_swap (l : List (Nat × Row)) (e : (Nat × Row) × (Nat × Row)) :
    Uses l (e.2,e.1) ↔ Uses l e := by
  constructor <;> rintro ⟨f,hf,h⟩ <;> refine ⟨f,hf,?_⟩
  · exact sameEdge_trans _ _ _ h (Or.inr rfl)
  · exact sameEdge_trans _ _ _ h (Or.inr rfl)

/-- Exact local undirected edge ledger for every ordinary/upper/lower block.
No block-edge allocation is supplied as an input. -/
theorem block_ledger {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat)
    (e : (Nat × Row) × (Nat × Row)) :
    Uses (block M s j) e ↔ ∃ label ∈ labels M s j, SameEdge (labelEdge M label) e := by
  unfold Uses block labels
  cases hk : M.kind j with
  | ordinary =>
    cases hs : s j <;> simp [steps,labelEdge,SameEdge,Prod.mk.injEq] <;> grind
  | upper i => simp [steps]
  | lower i =>
    have hj := M.kind_lower j i hk
    cases hs : s j <;> cases ht : s (M.upper i) <;>
      simp [ht,steps,labelEdge,SameEdge,Prod.mk.injEq,hj] <;> grind

theorem lower_injective {N k} (M : Matching N k) : Function.Injective M.lower := by
  intro i j h
  have hh := congrArg M.kind h
  rw [M.lower_kind,M.lower_kind] at hh
  exact Kind.lower.inj hh

theorem lower_ne_upper {N k} (M : Matching N k) (i j : Fin k) : M.lower i≠M.upper j := by
  intro h
  have hh := congrArg M.kind h
  rw [M.lower_kind,M.upper_kind] at hh
  contradiction

/-- Realized labels are injective as UNDIRECTED edges, not just ordered pairs. -/
theorem labelEdge_unique {N k} (M : Matching N k) (a b : Label k)
    (h : SameEdge (labelEdge M a) (labelEdge M b)) : a=b := by
  cases a with
  | chord i r => cases b with
    | chord j t =>
      rcases h with h | h
      · have hi : i=j := lower_injective M (congrArg (fun e => e.1.1) h)
        have hr : r=t := congrArg (fun e => e.1.2) h
        rw [hi,hr]
      · exact False.elim (lower_ne_upper M i j (congrArg (fun e => e.1.1) h))
    | vertical j t =>
      have ho := M.ordered i
      simp only [SameEdge,labelEdge,Prod.mk.injEq] at h
      rcases h with h | h <;> omega
  | vertical i r => cases b with
    | chord j t =>
      have ho := M.ordered j
      simp only [SameEdge,labelEdge,Prod.mk.injEq] at h
      rcases h with h | h <;> omega
    | vertical j t =>
      simp only [SameEdge,labelEdge,Prod.mk.injEq] at h
      rcases h with h | h
      · rw [h.1.1,Row.primary.inj h.1.2]
      · cases h.1.2

def labelOwner {N k} (M : Matching N k) : Label k → Nat
  | .chord i _ => M.lower i
  | .vertical j _ => match M.kind j with
    | .upper i => M.lower i
    | _ => j

theorem labels_owner {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat)
    (a : Label k) (ha : a ∈ labels M s j) : labelOwner M a=j := by
  unfold labels at ha
  cases hk : M.kind j with
  | ordinary =>
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl <;> simp [labelOwner,hk]
  | upper i => simp [hk] at ha
  | lower i =>
    have hj := M.kind_lower j i hk
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp [labelOwner,M.upper_kind,M.lower_kind,hj]

theorem labels_nodup {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat) :
    (labels M s j).Nodup := by
  unfold labels
  cases hk : M.kind j with
  | ordinary => cases s j <;> simp
  | upper i => simp
  | lower i =>
    have hj := M.kind_lower j i hk
    have hne : j≠M.upper i := by have ho := M.ordered i; omega
    simp [hne]

theorem flat_labels_nodup {N k} (M : Matching N k) (s : Nat → Bool)
    (indices : List Nat) (hi : indices.Nodup) : (indices.flatMap (labels M s)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _; exact labels_nodup M s j
  · apply hi.imp
    intro i j hij a ha b hb he
    have hia := labels_owner M s i a ha
    have hjb := labels_owner M s j b hb
    rw [he] at hia
    exact hij (hia.symm.trans hjb)

/-- Exact local allocation labels have one global scan-block owner, and their
realized undirected edges never coincide across two different labels. -/
theorem scan_local_labels_unique {N k} (M : Matching N k) (s : Nat → Bool) :
    ((middle N).flatMap (labels M s)).Nodup ∧
      ∀ a b, SameEdge (labelEdge M a) (labelEdge M b) → a=b :=
  ⟨flat_labels_nodup M s _ (middle_nodup N),labelEdge_unique M⟩

/-- The sole new edge created by joining two nonempty literal words. -/
def bridges {α : Type} (l r : List α) : List (α×α) :=
  match l.getLast?, r.head? with
  | some a, some b => [(a,b)]
  | _, _ => []

theorem steps_cons_cons {α : Type} (a b : α) (l : List α) :
    steps (a::b::l)=(a,b)::steps (b::l) := rfl

/-- Exact edge ledger of an append, retaining its actual boundary edge. -/
theorem steps_append {α : Type} (l r : List α) :
    steps (l++r)=steps l++bridges l r++steps r := by
  induction l with
  | nil => simp [steps,bridges]
  | cons a l ih =>
    cases l with
    | nil => cases r <;> simp [steps,bridges]
    | cons b l =>
      simp only [List.cons_append,steps_cons_cons,List.cons_append] at ih ⊢
      rw [ih]
      simp [bridges,List.getLast?_cons_cons]

theorem uses_append (l r : List (Nat×Row)) (e : (Nat×Row)×(Nat×Row)) :
    Uses (l++r) e ↔ Uses l e ∨
      (∃ f, f∈bridges l r ∧ SameEdge f e) ∨ Uses r e := by
  simp only [Uses,steps_append,List.mem_append]
  constructor
  · rintro ⟨f,(hf|hf)|hf,he⟩
    · exact Or.inl ⟨f,hf,he⟩
    · exact Or.inr (Or.inl ⟨f,hf,he⟩)
    · exact Or.inr (Or.inr ⟨f,hf,he⟩)
  · rintro (⟨f,hf,he⟩|⟨f,hf,he⟩|⟨f,hf,he⟩)
    · exact ⟨f,Or.inl (Or.inl hf),he⟩
    · exact ⟨f,Or.inl (Or.inr hf),he⟩
    · exact ⟨f,Or.inr hf,he⟩

/-- Actual parent-0 edge connecting one descending block to the remaining
scan. This includes the final connection to base position zero. -/
theorem block_scan_bridge {N k} (M : Matching N k) (n : Nat) (hn : n+1≤N-2) :
    bridges (block M (state M) (n+1)) (scanTail M n) =
      [((n+1,.primary (state M n)),(n,.primary (state M n)))] := by
  unfold bridges
  rw [block_last M (n+1) (by omega),scanTail_head]
  simp

def scanEdges {N k} (M : Matching N k) : Nat → List ((Nat×Row)×(Nat×Row))
  | 0 => []
  | n+1 => steps (block M (state M) (n+1)) ++
      [((n+1,.primary (state M n)),(n,.primary (state M n)))] ++ scanEdges M n

/-- Exact full descending scan edge list: local block edges and literal
parent-0 connectors, with no assumed scan edge allocation. -/
theorem scanTail_steps {N k} (M : Matching N k) (n : Nat) (hn : n≤N-2) :
    steps (scanTail M n)=scanEdges M n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hword : scanTail M (n+1)=block M (state M) (n+1)++scanTail M n := by
      simp [scanTail,descending,List.append_assoc]
    rw [hword,steps_append,block_scan_bridge M n hn,ih (by omega)]
    rfl

theorem word_steps {N k} (M : Matching N k) :
    steps (word M (state M)) =
      [((N-1,.primary false),(N-2,.primary false))]++scanEdges M (N-2) := by
  have hw : word M (state M) = [(N-1,.primary false)]++scanTail M (N-2) := by
    simp only [word,scanTail,descending_eq,middle,List.append_assoc]
  rw [hw,steps_append,scanTail_steps M (N-2) (by omega)]
  have hb : bridges [(N-1,.primary false)] (scanTail M (N-2)) =
      [((N-1,.primary false),(N-2,.primary false))] := by
    unfold bridges
    rw [scanTail_head,state_initial]
    rfl
  rw [hb]
  rfl

/-- A selected nonzero-factor chord cannot coincide with any actual parent-0
cyclic edge. This separates local scan repairs from all parent-0 bridges. -/
theorem selected_not_base {V R k N hN} (d : DecompositionData V R (k+1) N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList d.cycles selected).Nodup)
    (i : Fin k) (t : Fin N) :
    ¬SameEdge
      (vertexAt (closeSelected (d.cycles 0) (selected 0))
        ((normalizedMatching d.cycles selected hn).lower i),
       vertexAt (closeSelected (d.cycles 0) (selected 0))
        ((normalizedMatching d.cycles selected hn).upper i))
      ((closeSelected (d.cycles 0) (selected 0)).cycle t,
       (closeSelected (d.cycles 0) (selected 0)).cycle (successor hN t)) := by
  intro he
  have hs := normalized_selected_sameEdge d.cycles selected hn i
  have hh := sameEdge_trans _ _ _ (sameEdge_symm _ _ hs) he
  have hr := rotate_step (d.cycles 0) (successor hN (selected 0)) t
  change _ = _ at hr
  change SameEdge _ ((rotate (d.cycles 0) (successor hN (selected 0))).cycle t,
    (rotate (d.cycles 0) (successor hN (selected 0))).cycle (successor hN t)) at hh
  rw [hr] at hh
  have hi := (d.unique i.succ (selected i.succ) 0 _ hh).1
  have hv := congrArg Fin.val hi
  simp at hv

theorem steps_reverse {α : Type} (l : List α) :
    steps l.reverse=(steps l).reverse.map (fun e => (e.2,e.1)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l =>
      rw [List.reverse_cons,steps_append,ih]
      simp [bridges,List.getLast?_reverse,steps]

def openRows (N row : Nat) : List ((Nat×Nat)×(Nat×Nat)) :=
  (List.range (N-1)).map (fun j => ((j,row),(j+1,row)))

theorem P_steps (N row : Nat) : steps (P N row)=openRows N row := by
  induction N with
  | zero => rfl
  | succ N ih =>
    cases N with
    | zero => rfl
    | succ n =>
      have hp : P (n+1+1) row = P (n+1) row++[(n+1,row)] := by
        simp [P,List.range_succ,List.map_append]
      rw [hp,steps_append,ih]
      have hb : bridges (P (n+1) row) [(n+1,row)] = [((n,row),(n+1,row))] := by
        unfold bridges
        rw [P_last _ _ (by omega)]
        simp
      rw [hb]
      simp [openRows,List.range_succ,List.map_append,steps]

def KEdges (N : Nat) (s : Bool) : List ((Nat×Nat)×(Nat×Nat)) :=
  openRows N 0 ++ [((N-1,0),(N-1,oRow s))] ++
    (openRows N (oRow s)).reverse.map (fun e => (e.2,e.1)) ++
    [((0,oRow s),(0,3))] ++ openRows N 3 ++
    [((N-1,3),(N-1,sRow s))] ++
    (openRows N (sRow s)).reverse.map (fun e => (e.2,e.1))

/-- Complete literal Ki open edge ledger, including all three row joins. -/
theorem K_steps (N : Nat) (s : Bool) (hN : 0<N) :
    steps (K N s)=KEdges N s := by
  simp only [K,steps_append,steps_reverse,P_steps]
  simp [bridges,List.getLast?_append,List.getLast?_reverse,List.head?_reverse,
    P_last _ _ hN,P_head _ _ hN,KEdges,List.append_assoc]

def closedEdges {α : Type} (l : List α) : List (α×α) := steps l++bridges l l

/-- The four-row cycle's full ledger deletes the parent closing horizontal
edge in every row and inserts exactly four endpoint row edges. -/
theorem K_closedEdges (N : Nat) (s : Bool) (hN : 0<N) :
    closedEdges (K N s)=KEdges N s++[((0,sRow s),(0,0))] := by
  rw [closedEdges,K_steps N s hN]
  unfold bridges
  rw [K_last _ _ hN,K_head _ _ hN]

def Occurs {α : Type} (edges : List (α×α)) (e : α×α) : Prop :=
  ∃ f, f∈edges ∧ SameEdge f e

theorem occurs_append {α : Type} (l r : List (α×α)) (e : α×α) :
    Occurs (l++r) e ↔ Occurs l e ∨ Occurs r e := by
  simp only [Occurs,List.mem_append]
  constructor
  · rintro ⟨f,hf|hf,he⟩
    · exact Or.inl ⟨f,hf,he⟩
    · exact Or.inr ⟨f,hf,he⟩
  · rintro (⟨f,hf,he⟩|⟨f,hf,he⟩)
    · exact ⟨f,Or.inl hf,he⟩
    · exact ⟨f,Or.inr hf,he⟩

theorem occurs_reverse_swap {α : Type} (l : List (α×α)) (e : α×α) :
    Occurs (l.reverse.map (fun f => (f.2,f.1))) e ↔ Occurs l e := by
  constructor
  · rintro ⟨f,hf,he⟩
    obtain ⟨g,hg,hgf⟩ := List.mem_map.mp hf
    refine ⟨g,List.mem_reverse.mp hg,?_⟩
    subst f
    exact sameEdge_trans _ _ _ (Or.inr rfl) he
  · rintro ⟨f,hf,he⟩
    refine ⟨(f.2,f.1),List.mem_map.mpr ⟨f,List.mem_reverse.mpr hf,rfl⟩,?_⟩
    exact sameEdge_trans _ _ _ (Or.inr rfl) he

theorem openRows_occurs (N row : Nat) (e : (Nat×Nat)×(Nat×Nat)) :
    Occurs (openRows N row) e ↔
      ∃ j, j+1<N ∧ SameEdge ((j,row),(j+1,row)) e := by
  constructor
  · rintro ⟨f,hf,he⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    exact ⟨j,by have := List.mem_range.mp hj; omega,he⟩
  · rintro ⟨j,hj,he⟩
    exact ⟨_,List.mem_map.mpr ⟨j,List.mem_range.mpr (by omega),rfl⟩,he⟩

def KConnectors (N : Nat) (s : Bool) : List ((Nat×Nat)×(Nat×Nat)) :=
  [((N-1,0),(N-1,oRow s)),((0,oRow s),(0,3)),
   ((N-1,3),(N-1,sRow s)),((0,sRow s),(0,0))]

/-- Every cyclic Ki edge belongs exactly to the four open horizontal row
copies or to its four explicit endpoint connectors; no other edge occurs. -/
theorem K_occurs (N : Nat) (s : Bool) (hN : 0<N) (e : (Nat×Nat)×(Nat×Nat)) :
    Occurs (closedEdges (K N s)) e ↔
      (∃ row j, row<4 ∧ j+1<N ∧ SameEdge ((j,row),(j+1,row)) e) ∨
      Occurs (KConnectors N s) e := by
  rw [K_closedEdges N s hN]
  simp only [KEdges,occurs_append,occurs_reverse_swap,openRows_occurs]
  cases s <;> simp only [sRow,oRow,rowNat,rowIndex,Bool.not_false,Bool.not_true,KConnectors]
  all_goals
    simp only [Occurs,List.mem_cons,List.not_mem_nil,or_false,
      exists_eq_left] at *
    constructor
    · intro h
      rcases h with (((((((h|h)|h)|h)|h)|h)|h)|h)
      all_goals first
        | exact Or.inr (by grind)
        | obtain ⟨j,hj,he⟩ := h; exact Or.inl ⟨_,j,by omega,hj,he⟩
    · rintro (⟨row,j,hr,hj,he⟩|h)
      · have hh : row=0 ∨ row=1 ∨ row=2 ∨ row=3 := by omega
        rcases hh with rfl|rfl|rfl|rfl <;> grind
      · grind

theorem steps_map {α β : Type} (f : α→β) (l : List α) :
    steps (l.map f)=(steps l).map (fun e => (f e.1,f e.2)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simpa only [List.map_cons,steps_cons_cons] using congrArg (List.cons (f a,f b)) ih

theorem bridges_map {α β : Type} (f : α→β) (l r : List α) :
    bridges (l.map f) (r.map f)=(bridges l r).map (fun e => (f e.1,f e.2)) := by
  simp only [bridges,List.getLast?_map,List.head?_map]
  cases l.getLast? <;> cases r.head? <;> rfl

theorem closedEdges_map {α β : Type} (f : α→β) (l : List α) :
    closedEdges (l.map f)=(closedEdges l).map (fun e => (f e.1,f e.2)) := by
  simp only [closedEdges,steps_map,bridges_map,List.map_append]

theorem actualK_edges {V R N hN} (C : CycleData V R N hN) (s : Bool) :
    closedEdges (actualK C s)=
      (KEdges N s++[((0,sRow s),(0,0))]).map
        (fun e : (Nat×Nat)×(Nat×Nat) => (interpret C e.1,interpret C e.2)) := by
  rw [actualK,closedEdges_map,K_closedEdges N s hN]

theorem bridges_self {α : Type} {L : Nat} (hL : 0<L) (l : List α) (hl : l.length=L) :
    bridges l l=[(l[L-1]'(by omega),l[0]'(by omega))] := by
  unfold bridges
  rw [List.getLast?_eq_getElem?,List.head?_eq_getElem?]
  have hi : l.length-1=L-1 := by omega
  rw [hi]
  rw [List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem (by omega)]

/-- Exact equivalence between the literal closed edge list and actual cyclic
positions; this also includes the last-first edge. -/
theorem closedEdges_positions {α : Type} {L : Nat} (hL : 0<L) (l : List α)
    (hl : l.length=L) (e : α×α) :
    Occurs (closedEdges l) e ↔ ∃ t : Fin L,
      SameEdge (l[t.val]'(by have := t.isLt; omega),
        l[(successor hL t).val]'(by have := (successor hL t).isLt; omega)) e := by
  rw [closedEdges,occurs_append,bridges_self hL l hl]
  constructor
  · rintro (⟨f,hf,he⟩|⟨f,hf,he⟩)
    · obtain ⟨j,hj,hf⟩ := List.mem_iff_getElem.mp hf
      have hb : j+1<L := by
        simp only [steps,List.length_zip,List.length_tail,hl] at hj
        omega
      refine ⟨⟨j,by omega⟩,?_⟩
      have hs : (successor hL ⟨j,by omega⟩).val=j+1 := by
        rw [successor_val,ite_eq_left hb]
      simp only [steps,List.getElem_zip,List.getElem_tail] at hf
      rw [←hf] at he
      simpa only [hs] using he
    · have hf' := List.mem_singleton.mp hf
      subst f
      refine ⟨⟨L-1,by omega⟩,?_⟩
      have hs : (successor hL ⟨L-1,by omega⟩).val=0 := by
        rw [successor_val,ite_eq_right (show ¬(L-1)+1<L by omega)]
      simpa only [hs] using he
  · rintro ⟨t,he⟩
    by_cases ht : t.val+1<L
    · left
      have hs : (successor hL t).val=t.val+1 := by rw [successor_val,ite_eq_left ht]
      refine ⟨(l[t.val]'(by omega),l[t.val+1]'(by omega)),?_,?_⟩
      · apply List.mem_iff_getElem.mpr
        have hh : t.val<(steps l).length := by
          simp only [steps,List.length_zip,List.length_tail,hl]; omega
        exact ⟨t.val,hh,by simp [steps,List.getElem_zip,List.getElem_tail]⟩
      · simpa only [hs] using he
    · right
      have hv : t.val=L-1 := by have := t.isLt; omega
      have hs : (successor hL t).val=0 := by rw [successor_val,ite_eq_right ht]
      exact ⟨(l[L-1]'(by omega),l[0]'(by omega)),by simp,by simpa only [hv,hs] using he⟩

theorem fourRowCycle_positions {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    Occurs (closedEdges (actualK C s)) e ↔ ∃ t,
      SameEdge ((fourRowCycle C s hsym).cycle t,
        (fourRowCycle C s hsym).cycle (successor (show 0<4*N by omega) t)) e := by
  exact closedEdges_positions (show 0<4*N by omega) (actualK C s) (actualK_length C s) e

theorem occurs_map_same {α β : Type} (f : α→β) (edges : List (α×α)) (e : α×α)
    (he : Occurs edges e) :
    Occurs (edges.map (fun g => (f g.1,f g.2))) (f e.1,f e.2) := by
  obtain ⟨g,hg,hge⟩ := he
  refine ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
  rcases hge with hge|hge
  · exact Or.inl (congrArg (fun g => (f g.1,f g.2)) hge)
  · exact Or.inr (congrArg (fun g => (f g.1,f g.2)) hge)

theorem sameEdge_map {α β : Type} (f : α→β) {a b : α×α} (h : SameEdge a b) :
    SameEdge (f a.1,f a.2) (f b.1,f b.2) := by
  rcases h with h|h
  · exact Or.inl (congrArg (fun g => (f g.1,f g.2)) h)
  · exact Or.inr (congrArg (fun g => (f g.1,f g.2)) h)

theorem interpret_open_step {V R N hN} (C : CycleData V R N hN) (t : Fin N)
    (ht : t.val+1<N) (row : Fin 4) :
    (interpret C (t.val,row.val),interpret C (t.val+1,row.val)) =
      ((C.cycle t,row),(C.cycle (successor hN t),row)) := by
  have hs : (successor hN t).val=t.val+1 := by rw [successor_val,ite_eq_left ht]
  have htf : (⟨t.val%N,Nat.mod_lt _ hN⟩ : Fin N)=t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
  have hsf : (⟨(t.val+1)%N,Nat.mod_lt _ hN⟩ : Fin N)=successor hN t := by
    apply Fin.ext; rw [hs]; exact Nat.mod_eq_of_lt ht
  have hrf : (⟨row.val%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=row :=
    Fin.ext (Nat.mod_eq_of_lt row.isLt)
  simp only [interpret,vertexAt,htf,hsf,hrf]

/-- Every nonselected edge of every nonzero parent factor appears in Ki in
each of the four actual rows, at an actual cyclic position. -/
theorem other_unselected_cover {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hsym : ∀ u v, R u v → R v u)
    (i : Fin k) (t : Fin N) (ht : t≠selected i.succ) (row : Fin 4) :
    ∃ q, SameEdge
      ((otherCycle cycles selected hn hsym i).cycle q,
       (otherCycle cycles selected hn hsym i).cycle (successor (show 0<4*N by omega) q))
      (((cycles i.succ).cycle t,row),((cycles i.succ).cycle (successor hN t),row)) := by
  obtain ⟨u,hu⟩ := originalIndex_surjective cycles selected i t
  have hub : u.val+1<N := by
    have hlast := originalIndex_selected_iff cycles selected i u
    have huLt := u.isLt
    by_cases h : u.val+1<N
    · exact h
    · have hv : u.val=N-1 := by omega
      have hsel := hlast.mpr (Fin.ext hv)
      exact False.elim (ht (hu.symm.trans hsel))
  let C := normalizedOther cycles selected hsym i
  let s := state (normalizedMatching cycles selected hn) ((normalizedMatching cycles selected hn).upper i)
  have hc : Occurs (closedEdges (K N s)) ((u.val,row.val),(u.val+1,row.val)) :=
    (K_occurs N s hN _).mpr (Or.inl ⟨row.val,u.val,row.isLt,hub,Or.inl rfl⟩)
  have hm := occurs_map_same (interpret C) _ _ hc
  rw [←closedEdges_map] at hm
  change Occurs (closedEdges (actualK C s)) _ at hm
  rw [interpret_open_step C u hub row] at hm
  obtain ⟨q,hq⟩ := (fourRowCycle_positions C s hsym _).mp hm
  refine ⟨q,sameEdge_trans _ _ _ hq ?_⟩
  have hp := sameEdge_map (fun v : V => (v,row))
    (normalizedOther_step cycles selected hsym i u)
  rw [hu] at hp
  exact hp

/-- A genuinely horizontal edge in a four-row tour must come from a
nonclosing edge of the normalized parent tour. Endpoint joins cannot create
any horizontal edge. -/
theorem fourRow_horizontal_only {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) (u v : V) (row : Fin 4) (hne : u≠v)
    (q : Fin (4*N))
    (he : SameEdge ((fourRowCycle C s hsym).cycle q,
      (fourRowCycle C s hsym).cycle (successor (show 0<4*N by omega) q)) ((u,row),(v,row))) :
    ∃ t : Fin N, t.val+1<N ∧ SameEdge (C.cycle t,C.cycle (successor hN t)) (u,v) := by
  have hocc := (fourRowCycle_positions C s hsym _).mpr ⟨q,he⟩
  obtain ⟨f,hf,hfe⟩ := hocc
  rw [actualK,closedEdges_map] at hf
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have hn := (K_occurs N s hN g).mp ⟨g,hg,Or.inl rfl⟩
  rcases hn with ⟨r,j,hr,hj,hg⟩|⟨g',hg',hgg⟩
  · let t : Fin N := ⟨j,by omega⟩
    let r' : Fin 4 := ⟨r,hr⟩
    have hm := sameEdge_map (interpret C) hg
    have hh := sameEdge_trans _ _ _ hm hfe
    rw [interpret_open_step C t hj r'] at hh
    refine ⟨t,hj,?_⟩
    exact sameEdge_map (fun x : V×Fin 4 => x.1) hh
  · have hm := sameEdge_map (interpret C) hgg
    have hh := sameEdge_trans _ _ _ hm hfe
    have heq : (interpret C g'.1).1=(interpret C g'.2).1 := by
      simp only [KConnectors,List.mem_cons,List.not_mem_nil,or_false] at hg'
      rcases hg' with rfl|rfl|rfl|rfl <;> rfl
    rcases hh with hh|hh
    · have hu := congrArg (fun e => e.1.1) hh
      have hv := congrArg (fun e => e.2.1) hh
      exact False.elim (hne (hu.symm.trans (heq.trans hv)))
    · have hv := congrArg (fun e => e.1.1) hh
      have hu := congrArg (fun e => e.2.1) hh
      exact False.elim (hne (hu.symm.trans (heq.symm.trans hv)))

/-- Exact horizontal ownership among all Ki factors: Ki owns precisely the
four row copies of its own parent's nonselected edges. -/
theorem other_horizontal_iff {V R k N hN} (d : DecompositionData V R (k+1) N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList d.cycles selected).Nodup)
    (i : Fin k) (f : Fin (k+1)) (t : Fin N) (row : Fin 4) :
    (∃ q, SameEdge
      ((otherCycle d.cycles selected hn d.symmetric i).cycle q,
       (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) q))
      (((d.cycles f).cycle t,row),((d.cycles f).cycle (successor hN t),row))) ↔
      f=i.succ ∧ t≠selected f := by
  constructor
  · rintro ⟨q,hq⟩
    have hne : (d.cycles f).cycle t≠(d.cycles f).cycle (successor hN t) := by
      intro he
      have ha := (d.cycles f).adjacent t
      rw [he] at ha
      exact d.loopfree _ ha
    obtain ⟨a,ha,hp⟩ := fourRow_horizontal_only (normalizedOther d.cycles selected d.symmetric i)
      (state (normalizedMatching d.cycles selected hn) ((normalizedMatching d.cycles selected hn).upper i))
      d.symmetric _ _ row hne q hq
    have hm := normalizedOther_step d.cycles selected d.symmetric i a
    have hh := sameEdge_trans _ _ _ (sameEdge_symm _ _ hm) hp
    obtain ⟨hif,hat⟩ := d.unique i.succ (originalIndex d.cycles selected i a) f t hh
    refine ⟨hif.symm,?_⟩
    intro hsel
    rw [←hif] at hsel
    have hi := (originalIndex_selected_iff d.cycles selected i a).mp (hat.trans hsel)
    have hv := congrArg Fin.val hi
    change a.val=N-1 at hv
    have hb := a.isLt
    omega
  · rintro ⟨rfl,ht⟩
    exact other_unselected_cover d.cycles selected hn d.symmetric i t ht row

def actualKConnectors {V R N hN} (C : CycleData V R N hN) (s : Bool) :
    List ((V×Fin 4)×(V×Fin 4)) :=
  (KConnectors N s).map (fun e => (interpret C e.1,interpret C e.2))

/-- The only vertical edges of Ki are its four actual endpoint connectors.
This characterizes their occurrence at genuine cyclic edge positions. -/
theorem fourRow_vertical_iff {V R N hN} (C : CycleData V R N hN) (s : Bool)
    (hsym : ∀ u v, R u v → R v u) (u : V) (a b : Fin 4) :
    (∃ q, SameEdge ((fourRowCycle C s hsym).cycle q,
      (fourRowCycle C s hsym).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) ↔
    Occurs (actualKConnectors C s) ((u,a),(u,b)) := by
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨f,hf,hfe⟩ := (fourRowCycle_positions C s hsym _).mpr ⟨q,hq⟩
    rw [actualK,closedEdges_map] at hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    rcases (K_occurs N s hN g).mp ⟨g,hg,Or.inl rfl⟩ with
      ⟨r,j,hr,hj,hg⟩|⟨g',hg',hgg⟩
    · let t : Fin N := ⟨j,by omega⟩
      let r' : Fin 4 := ⟨r,hr⟩
      have hh := sameEdge_trans _ _ _ (sameEdge_map (interpret C) hg) hfe
      rw [interpret_open_step C t hj r'] at hh
      have heq : C.cycle t=C.cycle (successor hN t) := by
        rcases hh with hh|hh
        · exact (congrArg (fun e => e.1.1) hh).trans (congrArg (fun e => e.2.1) hh).symm
        · exact (congrArg (fun e => e.1.1) hh).trans (congrArg (fun e => e.2.1) hh).symm
      have hi := congrArg Fin.val (cycle_injective C heq)
      have hs : (successor hN t).val=t.val+1 := by rw [successor_val,ite_eq_left hj]
      rw [hs] at hi
      omega
    · exact ⟨_,List.mem_map.mpr ⟨g',hg',rfl⟩,
        sameEdge_trans _ _ _ (sameEdge_map (interpret C) hgg) hfe⟩
  · rintro ⟨g,hg,hge⟩
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    have hc : Occurs (closedEdges (K N s)) f :=
      (K_occurs N s hN f).mpr (Or.inr ⟨f,hf,Or.inl rfl⟩)
    have hm := occurs_map_same (interpret C) _ _ hc
    rw [←closedEdges_map] at hm
    change Occurs (closedEdges (actualK C s)) _ at hm
    obtain ⟨g,hg,hgf⟩ := hm
    exact (fourRowCycle_positions C s hsym _).mp ⟨g,hg,sameEdge_trans _ _ _ hgf hge⟩

theorem interpret_index {V R N hN} (C : CycleData V R N hN) (t : Fin N) (r : Fin 4) :
    interpret C (t.val,r.val)=(C.cycle t,r) := by
  have ht : (⟨t.val%N,Nat.mod_lt _ hN⟩ : Fin N)=t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
  have hr : (⟨r.val%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
  simp only [interpret,vertexAt,ht,hr]

/-- Ki's physical vertical ledger in the common normalized base coordinates.
The lower endpoint owns o->3 and s->0; upper owns 0->o and 3->s. -/
theorem other_connectors {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hsym : ∀ u v, R u v → R v u) (i : Fin k) :
    let M := normalizedMatching cycles selected hn
    let C0 := closeSelected (cycles 0) (selected 0)
    let s := state M (M.upper i)
    actualKConnectors (normalizedOther cycles selected hsym i) s =
      [((vertexAt C0 (M.upper i),⟨0,by decide⟩),(vertexAt C0 (M.upper i),rowIndex (.primary (!s)))),
       ((vertexAt C0 (M.lower i),rowIndex (.primary (!s))),(vertexAt C0 (M.lower i),⟨3,by decide⟩)),
       ((vertexAt C0 (M.upper i),⟨3,by decide⟩),(vertexAt C0 (M.upper i),rowIndex (.primary s))),
       ((vertexAt C0 (M.lower i),rowIndex (.primary s)),(vertexAt C0 (M.lower i),⟨0,by decide⟩))] := by
  dsimp only
  let C := normalizedOther cycles selected hsym i
  have h0 := normalizedOther_zero cycles selected hn hsym i
  have hlast := normalizedOther_last cycles selected hn hsym i
  have hz (r : Fin 4) : interpret C (0,r.val)=(C.cycle ⟨0,hN⟩,r) := interpret_index C ⟨0,hN⟩ r
  have hl (r : Fin 4) : interpret C (N-1,r.val)=(C.cycle ⟨N-1,by omega⟩,r) :=
    interpret_index C ⟨N-1,by omega⟩ r
  cases hs : state (normalizedMatching cycles selected hn) ((normalizedMatching cycles selected hn).upper i)
  all_goals
    simp only [actualKConnectors,KConnectors,List.map_cons,List.map_nil,sRow,oRow,
      rowNat,rowIndex,Bool.not_false,Bool.not_true]
    change _ = _
    rw [hl ⟨0,by decide⟩,hl ⟨3,by decide⟩,hz ⟨0,by decide⟩,hz ⟨3,by decide⟩]
  · rw [hl ⟨2,by decide⟩,hl ⟨1,by decide⟩,hz ⟨2,by decide⟩,hz ⟨1,by decide⟩,h0,hlast]
  · rw [hl ⟨1,by decide⟩,hl ⟨2,by decide⟩,hz ⟨1,by decide⟩,hz ⟨2,by decide⟩,h0,hlast]

theorem other_vertical_iff {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hsym : ∀ u v, R u v → R v u)
    (i : Fin k) (u : V) (a b : Fin 4) :
    let M := normalizedMatching cycles selected hn
    let C0 := closeSelected (cycles 0) (selected 0)
    let s := rowIndex (.primary (state M (M.upper i)))
    let o := rowIndex (.primary (!(state M (M.upper i))))
    (∃ q, SameEdge ((otherCycle cycles selected hn hsym i).cycle q,
      (otherCycle cycles selected hn hsym i).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) ↔
      (u=vertexAt C0 (M.lower i) ∧
        (SameEdge (s,⟨0,by decide⟩) (a,b) ∨ SameEdge (o,⟨3,by decide⟩) (a,b))) ∨
      (u=vertexAt C0 (M.upper i) ∧
        (SameEdge (⟨0,by decide⟩,o) (a,b) ∨ SameEdge (⟨3,by decide⟩,s) (a,b))) := by
  dsimp only
  change (∃ q, SameEdge ((fourRowCycle _ _ hsym).cycle q,
    (fourRowCycle _ _ hsym).cycle _) _) ↔ _
  rw [fourRow_vertical_iff,other_connectors cycles selected hn hsym i]
  simp only [Occurs,List.mem_cons,List.not_mem_nil,or_false,or_and_right,exists_or,
    exists_eq_left,SameEdge,Prod.mk.injEq]
  grind

theorem vertexAt_injective_bounded {V R N hN} (C : CycleData V R N hN)
    {a b : Nat} (ha : a<N) (hb : b<N) (he : vertexAt C a=vertexAt C b) : a=b := by
  have hh := congrArg (fun v => (C.position v).val) he
  simp only [vertexAt,C.position_cycle] at hh
  simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hh

def endpointPosition {N k} (M : Matching N k) (i : Fin k) (b : Bool) : Nat :=
  if b then M.upper i else M.lower i

theorem endpointPosition_bound {N k} (M : Matching N k) (i : Fin k) (b : Bool) :
    endpointPosition M i b<N := by
  have ho := M.ordered i
  have hb := M.upper_bound i
  cases b <;> simp only [endpointPosition,Bool.false_eq_true,ite_false,ite_true] <;> omega

theorem endpointPosition_index {N k} (M : Matching N k) (i j : Fin k) (b c : Bool)
    (h : endpointPosition M i b=endpointPosition M j c) : i=j := by
  cases b <;> cases c <;> simp only [endpointPosition,Bool.false_eq_true,ite_false,ite_true] at h
  · exact lower_injective M h
  · exact False.elim (lower_ne_upper M i j h)
  · exact False.elim (lower_ne_upper M j i h.symm)
  · have hh := congrArg M.kind h
    rw [M.upper_kind,M.upper_kind] at hh
    exact Kind.upper.inj hh

theorem physical_endpoint_index {V R N hN k} (C : CycleData V R N hN)
    (M : Matching N k) (i j : Fin k) (b c : Bool)
    (h : vertexAt C (endpointPosition M i b)=vertexAt C (endpointPosition M j c)) : i=j :=
  endpointPosition_index M i j b c
    (vertexAt_injective_bounded C (endpointPosition_bound M i b) (endpointPosition_bound M j c) h)

/-- Every vertical edge occurring among Ki tours has only one Ki owner,
because the actual chosen parent endpoints are pairwise disjoint. -/
theorem other_vertical_unique {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (selected : Fin (k+1) → Fin N)
    (hn : (endpointList cycles selected).Nodup) (hsym : ∀ u v, R u v → R v u)
    (i j : Fin k) (u : V) (a b : Fin 4)
    (hi : ∃ q, SameEdge ((otherCycle cycles selected hn hsym i).cycle q,
      (otherCycle cycles selected hn hsym i).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b)))
    (hj : ∃ q, SameEdge ((otherCycle cycles selected hn hsym j).cycle q,
      (otherCycle cycles selected hn hsym j).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) : i=j := by
  have hi' := (other_vertical_iff cycles selected hn hsym i u a b).mp hi
  have hj' := (other_vertical_iff cycles selected hn hsym j u a b).mp hj
  let C := closeSelected (cycles 0) (selected 0)
  let M := normalizedMatching cycles selected hn
  rcases hi' with hi'|hi' <;> rcases hj' with hj'|hj'
  · exact physical_endpoint_index C M i j false false (hi'.1.symm.trans hj'.1)
  · exact physical_endpoint_index C M i j false true (hi'.1.symm.trans hj'.1)
  · exact physical_endpoint_index C M i j true false (hi'.1.symm.trans hj'.1)
  · exact physical_endpoint_index C M i j true true (hi'.1.symm.trans hj'.1)

/-- Full undirected edge injection for all genuine Ki factors. Together
with their horizontal and vertical classifiers this closes the Ki ledger. -/
theorem other_edge_unique {V R k N hN} (d : DecompositionData V R (k+1) N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList d.cycles selected).Nodup)
    (i j : Fin k) (q p : Fin (4*N))
    (he : SameEdge ((otherCycle d.cycles selected hn d.symmetric i).cycle q,
      (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) q))
      ((otherCycle d.cycles selected hn d.symmetric j).cycle p,
      (otherCycle d.cycles selected hn d.symmetric j).cycle (successor (show 0<4*N by omega) p))) :
    i=j ∧ q=p := by
  let x := (otherCycle d.cycles selected hn d.symmetric i).cycle q
  let y := (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) q)
  have hi : SameEdge ((otherCycle d.cycles selected hn d.symmetric i).cycle q,
      (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) q)) (x,y) := Or.inl rfl
  have hj : SameEdge ((otherCycle d.cycles selected hn d.symmetric j).cycle p,
      (otherCycle d.cycles selected hn d.symmetric j).cycle (successor (show 0<4*N by omega) p)) (x,y) :=
    sameEdge_symm _ _ he
  have ha : ActualGrid R x y := (otherCycle d.cycles selected hn d.symmetric i).adjacent q
  have hij : i=j := by
    rcases ha with ⟨hb,hr⟩|⟨hr,hb⟩
    · have hxy : (x,y)=((x.1,x.2),(x.1,y.2)) := by
        apply Prod.ext
        · rfl
        · exact Prod.ext hb.symm rfl
      have hi' : ∃ q, SameEdge ((otherCycle d.cycles selected hn d.symmetric i).cycle q,
          (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) q))
          ((x.1,x.2),(x.1,y.2)) := ⟨q,sameEdge_trans _ _ _ hi (Or.inl hxy)⟩
      have hj' : ∃ p, SameEdge ((otherCycle d.cycles selected hn d.symmetric j).cycle p,
          (otherCycle d.cycles selected hn d.symmetric j).cycle (successor (show 0<4*N by omega) p))
          ((x.1,x.2),(x.1,y.2)) := ⟨p,sameEdge_trans _ _ _ hj (Or.inl hxy)⟩
      exact other_vertical_unique d.cycles selected hn d.symmetric i j _ _ _ hi' hj'
    · obtain ⟨f,t,ht⟩ := d.cover x.1 y.1 hb
      have hm := sameEdge_map (fun v : V => (v,x.2)) ht
      have hx : ((x.1,x.2),(y.1,x.2))=(x,y) := by
        apply Prod.ext
        · rfl
        · exact Prod.ext rfl hr
      rw [hx] at hm
      have hip := sameEdge_trans _ _ _ hi (sameEdge_symm _ _ hm)
      have hjp := sameEdge_trans _ _ _ hj (sameEdge_symm _ _ hm)
      have hfi := ((other_horizontal_iff d selected hn i f t x.2).mp ⟨q,hip⟩).1
      have hfj := ((other_horizontal_iff d selected hn j f t x.2).mp ⟨p,hjp⟩).1
      exact Fin.succ_inj.mp (hfi.symm.trans hfj)
  subst j
  exact ⟨rfl,cyclic_position_unique (otherCycle d.cycles selected hn d.symmetric i) (by omega) q p he⟩

def WEdges {N k} (M : Matching N k) : List ((Nat×Nat)×(Nat×Nat)) :=
  ([((N-1,Row.primary false),(N-2,Row.primary false))]++scanEdges M (N-2)).map
    (fun e : (Nat×Row)×(Nat×Row) => ((e.1.1,rowNat e.1.2),(e.2.1,rowNat e.2.2)))

theorem W_steps {N k} (M : Matching N k) : steps (W M)=WEdges M := by
  rw [W,steps_map,word_steps]
  rfl

def R0Edges {N k} (M : Matching N k) : List ((Nat×Nat)×(Nat×Nat)) :=
  if state M 0 then
    openRows N 0 ++
    [((N-1,0),(N-1,2)),((N-1,2),(N-1,3)),((N-1,3),(0,3)),
     ((0,3),(0,1)),((0,1),(N-1,1))] ++ WEdges M ++ [((0,2),(0,0))]
  else
    openRows N 0 ++ [((N-1,0),(N-1,1))] ++ WEdges M ++
    [((0,1),(0,3)),((0,3),(N-1,3)),((N-1,3),(N-1,2)),
     ((N-1,2),(0,2)),((0,2),(0,0))]

def R1Edges {N k} (M : Matching N k) : List ((Nat×Nat)×(Nat×Nat)) :=
  if state M 0 then
    openRows N 3 ++
    [((N-1,3),(N-1,1)),((N-1,1),(N-1,0)),((N-1,0),(0,0)),((0,0),(0,1))] ++
    (WEdges M).reverse.map (fun e => (tau e.2,tau e.1)) ++
    [((N-1,2),(0,2)),((0,2),(0,3))]
  else
    openRows N 3 ++
    [((N-1,3),(N-1,1)),((N-1,1),(0,1)),((0,1),(0,0)),
     ((0,0),(N-1,0)),((N-1,0),(N-1,2))] ++
    (WEdges M).map (fun e => (tau e.1,tau e.2)) ++ [((0,2),(0,3))]

/-- Exact complete residual-0 cyclic edge list, including all repairs. -/
theorem R0_closedEdges {N k} (M : Matching N k) (hN : 0<N) :
    closedEdges (R0 M)=R0Edges M := by
  rw [closedEdges]
  have hb : bridges (R0 M) (R0 M)=[((0,2),(0,0))] := by
    unfold bridges
    rw [R0_last,R0_head _ hN]
  rw [hb]
  cases hs : state M 0
  all_goals
    simp only [R0,R0Edges,hs,Bool.false_eq_true,ite_false,ite_true,steps_append,P_steps,W_steps]
    simp [bridges,List.getLast?_append,P_last _ _ hN,W_head,W_last,
      finalRow,hs,steps,List.append_assoc]

/-- Exact complete residual-1 cyclic edge list, including reverse/tau scan
and last-first repairs in both final-state cases. -/
theorem R1_closedEdges {N k} (M : Matching N k) (hN : 0<N) :
    closedEdges (R1 M)=R1Edges M := by
  rw [closedEdges]
  have hb : bridges (R1 M) (R1 M)=[((0,2),(0,3))] := by
    unfold bridges
    rw [R1_last,R1_head _ hN]
  rw [hb]
  have hrl : ((List.map tau (W M)).reverse).getLast?=some (N-1,2) := by
    simp [List.getLast?_reverse,List.head?_map,W_head,tau]
  cases hs : state M 0
  all_goals
    simp only [R1,R1Edges,hs,Bool.false_eq_true,ite_false,ite_true,steps_append,P_steps,
      steps_map,steps_reverse,W_steps,List.map_map]
    simp [bridges,List.getLast?_append,P_last _ _ hN,W_head,W_last,
      List.head?_map,List.getLast?_map,List.head?_reverse,
      finalRow,hs,steps,tau,List.append_assoc,hrl,Function.comp_def,List.getLast?_cons]

theorem block_mapped_ledger {N k β} (M : Matching N k) (s : Nat→Bool) (j : Nat)
    (f : Nat×Row→β) (e : β×β) :
    Occurs ((steps (block M s j)).map (fun g => (f g.1,f g.2))) e ↔
      ∃ a, a∈labels M s j ∧ SameEdge (f (labelEdge M a).1,f (labelEdge M a).2) e := by
  constructor
  · rintro ⟨g,hg,hge⟩
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    obtain ⟨a,ha,heh⟩ := (block_ledger M s j h).mp ⟨h,hh,Or.inl rfl⟩
    exact ⟨a,ha,sameEdge_trans _ _ _ (sameEdge_map f heh) hge⟩
  · rintro ⟨a,ha,he⟩
    obtain ⟨g,hg,hga⟩ := (block_ledger M s j (labelEdge M a)).mpr ⟨a,ha,Or.inl rfl⟩
    exact ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,sameEdge_trans _ _ _ (sameEdge_map f hga) he⟩

theorem occurs_singleton {α : Type} (g e : α×α) : Occurs [g] e ↔ SameEdge g e := by
  simp [Occurs]

/-- Complete mapped descending-scan classifier: selected chord/vertical
block labels and the exactly indexed ordinary parent-0 bridges. -/
theorem scanEdges_mapped_occurs {N k β} (M : Matching N k) (n : Nat)
    (f : Nat×Row→β) (e : β×β) :
    Occurs ((scanEdges M n).map (fun g => (f g.1,f g.2))) e ↔
      (∃ j, j∈descending n ∧ ∃ a, a∈labels M (state M) j ∧
        SameEdge (f (labelEdge M a).1,f (labelEdge M a).2) e) ∨
      ∃ j, j<n ∧ SameEdge (f (j+1,.primary (state M j)),f (j,.primary (state M j))) e := by
  induction n with
  | zero => simp [scanEdges,descending,Occurs]
  | succ n ih =>
    simp only [scanEdges,List.map_append,List.map_cons,List.map_nil,occurs_append,
      block_mapped_ledger,occurs_singleton,ih]
    constructor
    · rintro ((h|h)|h)
      · exact Or.inl ⟨n+1,by simp [descending],h⟩
      · exact Or.inr ⟨n,by omega,h⟩
      · rcases h with ⟨j,hj,ha⟩|⟨j,hj,he⟩
        · exact Or.inl ⟨j,by simp [descending,hj],ha⟩
        · exact Or.inr ⟨j,by omega,he⟩
    · rintro (⟨j,hj,ha⟩|⟨j,hj,he⟩)
      · simp only [descending,List.mem_cons] at hj
        rcases hj with rfl|hj
        · exact Or.inl (Or.inl ha)
        · exact Or.inr (Or.inl ⟨j,hj,ha⟩)
      · by_cases h : j=n
        · subst j; exact Or.inl (Or.inr he)
        · exact Or.inr (Or.inr ⟨j,by omega,he⟩)

theorem actualR0_edges {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) :
    closedEdges (actualR0 cycles selected hn)=
      (R0Edges (normalizedMatching cycles selected hn)).map
        (fun e => (interpret (closeSelected (cycles 0) (selected 0)) e.1,
          interpret (closeSelected (cycles 0) (selected 0)) e.2)) := by
  rw [actualR0,closedEdges_map,R0_closedEdges _ hN]

theorem actualR1_edges {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) :
    closedEdges (actualR1 cycles selected hn)=
      (R1Edges (normalizedMatching cycles selected hn)).map
        (fun e => (interpret (closeSelected (cycles 0) (selected 0)) e.1,
          interpret (closeSelected (cycles 0) (selected 0)) e.2)) := by
  rw [actualR1,closedEdges_map,R1_closedEdges _ hN]

theorem residual0_positions {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    Occurs (closedEdges (actualR0 cycles selected hn)) e ↔
      ∃ t, SameEdge ((residualCycle0 cycles selected hn hN hsym).cycle t,
        (residualCycle0 cycles selected hn hN hsym).cycle (successor (show 0<4*N by omega) t)) e :=
  closedEdges_positions (show 0<4*N by omega) (actualR0 cycles selected hn)
    (actualR0_length cycles selected hn hN) e

theorem residual1_positions {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    Occurs (closedEdges (actualR1 cycles selected hn)) e ↔
      ∃ t, SameEdge ((residualCycle1 cycles selected hn hN hsym).cycle t,
        (residualCycle1 cycles selected hn hN hsym).cycle (successor (show 0<4*N by omega) t)) e :=
  closedEdges_positions (show 0<4*N by omega) (actualR1 cycles selected hn)
    (actualR1_length cycles selected hn hN) e

/-- Every actual residual-0 cyclic edge, including closing and boundary
edges, is characterized by the explicitly derived coordinate ledger. -/
theorem residual0_ledger {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ t, SameEdge ((residualCycle0 cycles selected hn hN hsym).cycle t,
      (residualCycle0 cycles selected hn hN hsym).cycle (successor (show 0<4*N by omega) t)) e) ↔
    Occurs ((R0Edges (normalizedMatching cycles selected hn)).map
      (fun g => (interpret (closeSelected (cycles 0) (selected 0)) g.1,
        interpret (closeSelected (cycles 0) (selected 0)) g.2))) e := by
  rw [←residual0_positions,actualR0_edges]

theorem residual1_ledger {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (hN : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ t, SameEdge ((residualCycle1 cycles selected hn hN hsym).cycle t,
      (residualCycle1 cycles selected hn hN hsym).cycle (successor (show 0<4*N by omega) t)) e) ↔
    Occurs ((R1Edges (normalizedMatching cycles selected hn)).map
      (fun g => (interpret (closeSelected (cycles 0) (selected 0)) g.1,
        interpret (closeSelected (cycles 0) (selected 0)) g.2))) e := by
  rw [←residual1_positions,actualR1_edges]

theorem W_local_cover {N k β} (M : Matching N k) (j : Nat) (hj : j∈middle N)
    (a : Label k) (ha : a∈labels M (state M) j) (f : Nat×Nat→β) :
    Occurs ((WEdges M).map (fun g => (f g.1,f g.2)))
      (f ((labelEdge M a).1.1,rowNat (labelEdge M a).1.2),
       f ((labelEdge M a).2.1,rowNat (labelEdge M a).2.2)) := by
  let F : Nat×Row→β := fun v => f (v.1,rowNat v.2)
  have hd : j∈descending (N-2) := by simpa only [descending_eq,middle] using hj
  have hh := (scanEdges_mapped_occurs M (N-2) F _).mpr
    (Or.inl ⟨j,hd,a,ha,Or.inl rfl⟩)
  simp only [WEdges,List.map_append,List.map_cons,List.map_nil,List.map_map,occurs_append]
  right
  simpa only [F,Function.comp_def] using hh

theorem R0_contains_W {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β)
    (he : Occurs ((WEdges M).map (fun g => (f g.1,f g.2))) e) :
    Occurs ((R0Edges M).map (fun g => (f g.1,f g.2))) e := by
  cases hs : state M 0 <;>
    simp only [R0Edges,hs,Bool.false_eq_true,ite_false,ite_true,List.map_append,occurs_append] <;>
    grind

theorem R1_contains_tauW {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β)
    (he : Occurs ((WEdges M).map (fun g => (f (tau g.1),f (tau g.2)))) e) :
    Occurs ((R1Edges M).map (fun g => (f g.1,f g.2))) e := by
  cases hs : state M 0
  · simp only [R1Edges,hs,Bool.false_eq_true,ite_false,List.map_append,List.map_map,
      Function.comp_def,occurs_append]
    exact Or.inl (Or.inr he)
  · have hr := (occurs_reverse_swap ((WEdges M).map (fun g => (f (tau g.1),f (tau g.2)))) e).mpr he
    simp only [R1Edges,hs,ite_true,List.map_append,List.map_map,occurs_append]
    left; right
    simpa only [List.map_reverse,List.map_map,Function.comp_def] using hr

theorem lower_chord_mem {N k} (M : Matching N k) (i : Fin k) :
    (.chord i .top : Label k)∈labels M (state M) (M.lower i) ∧
      (.chord i (.primary (!(state M (M.upper i)))) : Label k)∈labels M (state M) (M.lower i) := by
  simp [labels,M.lower_kind]

theorem lower_middle {N k} (M : Matching N k) (i : Fin k) : M.lower i∈middle N := by
  apply middle_mem.mpr
  have ho := M.ordered i
  have hb := M.upper_bound i
  exact ⟨M.lower_pos i,by omega⟩

/-- Residual0 covers the selected edge of every nonzero factor in
the two scan-chord rows 3 and other(upper-state). -/
theorem residual0_selected_cover {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (i : Fin k) (row : Row)
    (hr : row=.top ∨ row=(.primary
      (!(state (normalizedMatching cycles selected hn) ((normalizedMatching cycles selected hn).upper i))))) :
    ∃ q, SameEdge ((residualCycle0 cycles selected hn h2 hsym).cycle q,
      (residualCycle0 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) q))
      (((cycles i.succ).cycle (selected i.succ),rowIndex row),
       ((cycles i.succ).cycle (successor hN (selected i.succ)),rowIndex row)) := by
  let M := normalizedMatching cycles selected hn
  let C0 := closeSelected (cycles 0) (selected 0)
  have ha : (.chord i row : Label k)∈labels M (state M) (M.lower i) := by
    rcases hr with hr|hr
    · subst row; exact (lower_chord_mem M i).1
    · subst row; exact (lower_chord_mem M i).2
  have hrow : (⟨rowNat row%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=rowIndex row := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (rowIndex row).isLt
  have hw := W_local_cover M (M.lower i) (lower_middle M i) (.chord i row) ha (interpret C0)
  have hfull := R0_contains_W M (interpret C0) _ hw
  obtain ⟨q,hq⟩ := (residual0_ledger cycles selected hn h2 hsym _).mpr hfull
  refine ⟨q,sameEdge_trans _ _ _ hq ?_⟩
  have hp := sameEdge_map (fun v : V => (v,rowIndex row)) (normalized_selected_sameEdge cycles selected hn i)
  simpa only [labelEdge,interpret,hrow] using hp

/-- Residual1 covers the complementary selected-edge rows, obtained by
actual row reflection: 0 and the upper-state row. -/
theorem residual1_selected_cover {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (i : Fin k) (row : Row)
    (hr : row=.top ∨ row=(.primary
      (!(state (normalizedMatching cycles selected hn) ((normalizedMatching cycles selected hn).upper i))))) :
    ∃ q, SameEdge ((residualCycle1 cycles selected hn h2 hsym).cycle q,
      (residualCycle1 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) q))
      (((cycles i.succ).cycle (selected i.succ),flip4 (rowIndex row)),
       ((cycles i.succ).cycle (successor hN (selected i.succ)),flip4 (rowIndex row))) := by
  let M := normalizedMatching cycles selected hn
  let C0 := closeSelected (cycles 0) (selected 0)
  have ha : (.chord i row : Label k)∈labels M (state M) (M.lower i) := by
    rcases hr with hr|hr
    · subst row; exact (lower_chord_mem M i).1
    · subst row; exact (lower_chord_mem M i).2
  have hrow : (⟨(3-rowNat row)%4,Nat.mod_lt _ (by decide)⟩ : Fin 4)=flip4 (rowIndex row) := by
    apply Fin.ext
    change (3-(rowIndex row).val)%4=3-(rowIndex row).val
    exact Nat.mod_eq_of_lt (by have := (rowIndex row).isLt; omega)
  have hw := W_local_cover M (M.lower i) (lower_middle M i) (.chord i row) ha
    (fun v => interpret C0 (tau v))
  have hfull := R1_contains_tauW M (interpret C0) _ hw
  obtain ⟨q,hq⟩ := (residual1_ledger cycles selected hn h2 hsym _).mpr hfull
  refine ⟨q,sameEdge_trans _ _ _ hq ?_⟩
  have hp := sameEdge_map (fun v : V => (v,flip4 (rowIndex row)))
    (normalized_selected_sameEdge cycles selected hn i)
  simpa only [labelEdge,tau,interpret,hrow] using hp

def R0Repairs {N k} (M : Matching N k) : List ((Nat×Nat)×(Nat×Nat)) :=
  if state M 0 then
    [((N-1,0),(N-1,2)),((N-1,2),(N-1,3)),((N-1,3),(0,3)),
     ((0,3),(0,1)),((0,1),(N-1,1)),((0,2),(0,0))]
  else
    [((N-1,0),(N-1,1)),((0,1),(0,3)),((0,3),(N-1,3)),
     ((N-1,3),(N-1,2)),((N-1,2),(0,2)),((0,2),(0,0))]

def R1Repairs {N k} (M : Matching N k) : List ((Nat×Nat)×(Nat×Nat)) :=
  if state M 0 then
    [((N-1,3),(N-1,1)),((N-1,1),(N-1,0)),((N-1,0),(0,0)),
     ((0,0),(0,1)),((N-1,2),(0,2)),((0,2),(0,3))]
  else
    [((N-1,3),(N-1,1)),((N-1,1),(0,1)),((0,1),(0,0)),
     ((0,0),(N-1,0)),((N-1,0),(N-1,2)),((0,2),(0,3))]

theorem occurs_cons {α : Type} (g : α×α) (l : List (α×α)) (e : α×α) :
    Occurs (g::l) e ↔ SameEdge g e ∨ Occurs l e := by
  simp only [Occurs,List.mem_cons,or_and_right,exists_or,exists_eq_left]

theorem occurs_nil {α : Type} (e : α×α) : ¬Occurs [] e := by simp [Occurs]

theorem R0_mapped_occurs {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β) :
    Occurs ((R0Edges M).map (fun g => (f g.1,f g.2))) e ↔
      Occurs ((openRows N 0).map (fun g => (f g.1,f g.2))) e ∨
      Occurs ((WEdges M).map (fun g => (f g.1,f g.2))) e ∨
      Occurs ((R0Repairs M).map (fun g => (f g.1,f g.2))) e := by
  cases hs : state M 0 <;>
    simp only [R0Edges,R0Repairs,hs,Bool.false_eq_true,ite_false,ite_true,
      List.map_append,List.map_cons,List.map_nil,occurs_append,occurs_cons,occurs_nil,or_false] <;> grind only

theorem R1_mapped_occurs {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β) :
    Occurs ((R1Edges M).map (fun g => (f g.1,f g.2))) e ↔
      Occurs ((openRows N 3).map (fun g => (f g.1,f g.2))) e ∨
      Occurs ((WEdges M).map (fun g => (f (tau g.1),f (tau g.2)))) e ∨
      Occurs ((R1Repairs M).map (fun g => (f g.1,f g.2))) e := by
  have hr' : Occurs ((WEdges M).reverse.map (fun g => (f (tau g.2),f (tau g.1)))) e ↔
        Occurs ((WEdges M).map (fun g => (f (tau g.1),f (tau g.2)))) e := by
      simpa only [List.map_reverse,List.map_map,Function.comp_def] using
        occurs_reverse_swap ((WEdges M).map (fun g => (f (tau g.1),f (tau g.2)))) e
  cases hs : state M 0 <;>
    simp only [R1Edges,R1Repairs,hs,Bool.false_eq_true,ite_false,ite_true,
      List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
      occurs_append,occurs_cons,occurs_nil,or_false,hr'] <;> grind only

/-- W's complete mapped ownership classes: the initial horizontal bridge,
all exact local selected/vertical labels, and every descending C0 bridge. -/
theorem W_mapped_occurs {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β) :
    Occurs ((WEdges M).map (fun g => (f g.1,f g.2))) e ↔
      SameEdge (f (N-1,1),f (N-2,1)) e ∨
      (∃ j, j∈middle N ∧ ∃ a, a∈labels M (state M) j ∧
        SameEdge
          (f ((labelEdge M a).1.1,rowNat (labelEdge M a).1.2),
           f ((labelEdge M a).2.1,rowNat (labelEdge M a).2.2)) e) ∨
      ∃ j, j<N-2 ∧ SameEdge (f (j+1,sRow (state M j)),f (j,sRow (state M j))) e := by
  have hs := scanEdges_mapped_occurs M (N-2) (fun v => f (v.1,rowNat v.2)) e
  have hh := or_congr (Iff.rfl (a := SameEdge (f (N-1,1),f (N-2,1)) e)) hs
  simpa only [WEdges,List.map_append,List.map_cons,List.map_nil,List.map_map,
    Function.comp_def,occurs_append,occurs_singleton,descending_eq,middle,sRow,rowNat,rowIndex] using hh

def ScanClasses {N k β} (M : Matching N k) (f : Nat×Nat→β) (e : β×β) : Prop :=
  SameEdge (f (N-1,1),f (N-2,1)) e ∨
    (∃ j, j∈middle N ∧ ∃ a, a∈labels M (state M) j ∧
      SameEdge
        (f ((labelEdge M a).1.1,rowNat (labelEdge M a).1.2),
         f ((labelEdge M a).2.1,rowNat (labelEdge M a).2.2)) e) ∨
    ∃ j, j<N-2 ∧ SameEdge (f (j+1,sRow (state M j)),f (j,sRow (state M j))) e

def ResidualClasses {N k β} (M : Matching N k) (f : Nat×Nat→β)
    (b : Bool) (e : β×β) : Prop :=
  if b then
    Occurs ((openRows N 3).map (fun g => (f g.1,f g.2))) e ∨
      ScanClasses M (fun v => f (tau v)) e ∨
      Occurs ((R1Repairs M).map (fun g => (f g.1,f g.2))) e
  else
    Occurs ((openRows N 0).map (fun g => (f g.1,f g.2))) e ∨
      ScanClasses M f e ∨
      Occurs ((R0Repairs M).map (fun g => (f g.1,f g.2))) e

/-- Exact residual0 ownership classifier in actual physical coordinates:
row-zero parent edges, selected/vertical scan labels, parent-zero scan
bridges, and the explicit finite boundary repair list. -/
theorem residual0_classes {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ t, SameEdge ((residualCycle0 cycles selected hn h2 hsym).cycle t,
      (residualCycle0 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) t)) e) ↔
    ResidualClasses (normalizedMatching cycles selected hn)
      (interpret (closeSelected (cycles 0) (selected 0))) false e := by
  rw [residual0_ledger,R0_mapped_occurs,W_mapped_occurs]
  rfl

/-- Exact residual1 classifier; row reflection is applied to physical scan
coordinates, with reverse direction accounted for by undirected ownership. -/
theorem residual1_classes {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ t, SameEdge ((residualCycle1 cycles selected hn h2 hsym).cycle t,
      (residualCycle1 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) t)) e) ↔
    ResidualClasses (normalizedMatching cycles selected hn)
      (interpret (closeSelected (cycles 0) (selected 0))) true e := by
  rw [residual1_ledger,R1_mapped_occurs]
  rw [W_mapped_occurs (normalizedMatching cycles selected hn)
    (fun v => interpret (closeSelected (cycles 0) (selected 0)) (tau v)) e]
  rfl

def PositionEdge {N : Nat} (hN : 0<N) (x y : Nat) : Prop :=
  ∃ t : Fin N, SameEdge (t.val,(successor hN t).val) (x,y)

theorem position_forward {N} (hN : 0<N) (j : Nat) (hj : j+1<N) : PositionEdge hN j (j+1) := by
  refine ⟨⟨j,by omega⟩,Or.inl ?_⟩
  apply Prod.ext
  · rfl
  · rw [successor_val,ite_eq_left hj]

theorem position_reverse {N} (hN : 0<N) (j : Nat) (hj : j+1<N) : PositionEdge hN (j+1) j := by
  obtain ⟨t,ht⟩ := position_forward hN j hj
  exact ⟨t,sameEdge_trans _ _ _ ht (Or.inr rfl)⟩

theorem position_closing {N} (hN : 0<N) : PositionEdge hN (N-1) 0 := by
  refine ⟨⟨N-1,by omega⟩,Or.inl ?_⟩
  apply Prod.ext
  · rfl
  · rw [successor_val,ite_eq_right (show ¬(N-1)+1<N by omega)]

def BaseClass {N k} (M : Matching N k) (hN : 0<N) (x y : Nat) : Prop :=
  x=y ∨ PositionEdge hN x y ∨ ∃ i, SameEdge (M.lower i,M.upper i) (x,y)

theorem baseClass_sameEdge {N k} (M : Matching N k) (hN : 0<N) (x y u v : Nat)
    (hc : BaseClass M hN x y) (he : SameEdge (x,y) (u,v)) : BaseClass M hN u v := by
  rcases hc with hc|hc|⟨i,hc⟩
  · left
    rcases he with he|he <;> simp only [Prod.mk.injEq] at he <;> omega
  · right; left
    obtain ⟨t,ht⟩ := hc
    exact ⟨t,sameEdge_trans _ _ _ ht he⟩
  · exact Or.inr (Or.inr ⟨i,sameEdge_trans _ _ _ hc he⟩)

theorem scanClasses_base {N k} (M : Matching N k) (hN : 0<N) (h2 : 2≤N)
    (x y : Nat) (he : ScanClasses M (fun v => v.1) (x,y)) : BaseClass M hN x y := by
  rcases he with he|⟨j,hj,a,ha,he⟩|⟨j,hj,he⟩
  · have hp := position_reverse hN (N-2) (by omega)
    have hb : N-2+1=N-1 := by omega
    rw [hb] at hp
    exact baseClass_sameEdge M hN _ _ _ _ (Or.inr (Or.inl hp)) he
  · cases a with
    | chord i r => exact Or.inr (Or.inr ⟨i,he⟩)
    | vertical p b =>
      apply baseClass_sameEdge M hN p p x y (Or.inl rfl)
      exact he
  · exact baseClass_sameEdge M hN _ _ _ _
      (Or.inr (Or.inl (position_reverse hN j (by omega)))) he

theorem repair_boundary {N k} (M : Matching N k) (b : Bool)
    (g : (Nat×Nat)×(Nat×Nat))
    (hg : g∈(if b then R1Repairs M else R0Repairs M)) :
    g.1.1=g.2.1 ∨ (g.1.1=N-1 ∧ g.2.1=0) ∨ (g.1.1=0 ∧ g.2.1=N-1) := by
  cases b <;> cases hs : state M 0 <;>
    simp only [R0Repairs,R1Repairs,hs,Bool.false_eq_true,ite_false,ite_true,
      List.mem_cons,List.not_mem_nil,or_false] at hg
  all_goals rcases hg with rfl|rfl|rfl|rfl|rfl|rfl <;> simp

theorem residualClasses_base {N k} (M : Matching N k) (hN : 0<N) (h2 : 2≤N)
    (b : Bool) (x y : Nat) (he : ResidualClasses M (fun v => v.1) b (x,y)) : BaseClass M hN x y := by
  have hrepair (edges : List ((Nat×Nat)×(Nat×Nat)))
      (hed : edges=(if b then R1Repairs M else R0Repairs M))
      (he : Occurs (edges.map (fun g => (g.1.1,g.2.1))) (x,y)) : BaseClass M hN x y := by
    obtain ⟨g,hg,hge⟩ := he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    rw [hed] at hf
    rcases repair_boundary M b f hf with hh|⟨hx,hy⟩|⟨hx,hy⟩
    · exact baseClass_sameEdge M hN _ _ _ _ (Or.inl hh) hge
    · rw [hx,hy] at hge
      exact baseClass_sameEdge M hN _ _ _ _ (Or.inr (Or.inl (position_closing hN))) hge
    · rw [hx,hy] at hge
      have hp : PositionEdge hN 0 (N-1) := by
        obtain ⟨t,ht⟩ := position_closing hN
        exact ⟨t,sameEdge_trans _ _ _ ht (Or.inr rfl)⟩
      exact baseClass_sameEdge M hN _ _ _ _ (Or.inr (Or.inl hp)) hge
  have hopen (r : Nat) (he : Occurs ((openRows N r).map (fun g => (g.1.1,g.2.1))) (x,y)) :
      BaseClass M hN x y := by
    obtain ⟨g,hg,hge⟩ := he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    have hj := List.mem_range.mp hj
    exact baseClass_sameEdge M hN _ _ _ _ (Or.inr (Or.inl (position_forward hN j (by omega)))) hge
  cases b
  · simp only [ResidualClasses,Bool.false_eq_true,ite_false] at he
    rcases he with he|he|he
    · exact hopen 0 he
    · exact scanClasses_base M hN h2 x y he
    · exact hrepair _ rfl he
  · simp only [ResidualClasses,ite_true] at he
    rcases he with he|he|he
    · exact hopen 3 he
    · exact scanClasses_base M hN h2 x y he
    · exact hrepair _ rfl he

theorem closedEdges_vertices {α L} (hL : 0<L) (l : List α) (hl : l.length=L)
    (g : α×α) (hg : g∈closedEdges l) : g.1∈l ∧ g.2∈l := by
  rw [closedEdges,List.mem_append] at hg
  rcases hg with hg|hg
  · have hh := List.of_mem_zip hg
    exact ⟨hh.1,List.mem_of_mem_tail hh.2⟩
  · rw [bridges_self hL l hl] at hg
    have hg := List.mem_singleton.mp hg
    subst g
    exact ⟨List.getElem_mem _,List.getElem_mem _⟩

theorem residualEdges_bounds {N k} (M : Matching N k) (h2 : 2≤N) (b : Bool)
    (g : (Nat×Nat)×(Nat×Nat)) (hg : g∈(if b then R1Edges M else R0Edges M)) :
    (g.1.1<N ∧ g.1.2<4) ∧ (g.2.1<N ∧ g.2.2<4) := by
  cases b
  · simp only [Bool.false_eq_true,ite_false] at hg
    rw [←R0_closedEdges M (by omega)] at hg
    have hh := closedEdges_vertices (show 0<4*N by omega) (R0 M) (R0_length M h2) g hg
    exact ⟨(R0_exact M h2 _).mp hh.1,(R0_exact M h2 _).mp hh.2⟩
  · simp only [ite_true] at hg
    rw [←R1_closedEdges M (by omega)] at hg
    have hh := closedEdges_vertices (show 0<4*N by omega) (R1 M) (R1_length M h2) g hg
    exact ⟨(R1_exact M h2 _).mp hh.1,(R1_exact M h2 _).mp hh.2⟩

theorem residualEdges_classes {N k β} (M : Matching N k) (b : Bool)
    (f : Nat×Nat→β) (e : β×β) :
    Occurs ((if b then R1Edges M else R0Edges M).map (fun g => (f g.1,f g.2))) e ↔
      ResidualClasses M f b e := by
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    rw [R0_mapped_occurs,W_mapped_occurs]
    rfl
  · simp only [ite_true]
    rw [R1_mapped_occurs,W_mapped_occurs M (fun v => f (tau v)) e]
    rfl

theorem residualEdges_base {N k} (M : Matching N k) (hN : 0<N) (h2 : 2≤N) (b : Bool)
    (g : (Nat×Nat)×(Nat×Nat)) (hg : g∈(if b then R1Edges M else R0Edges M)) :
    BaseClass M hN g.1.1 g.2.1 := by
  have hc : Occurs ((if b then R1Edges M else R0Edges M).map (fun g => (g.1.1,g.2.1)))
      (g.1.1,g.2.1) := ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,Or.inl rfl⟩
  exact residualClasses_base M hN h2 b _ _ ((residualEdges_classes M b (fun v => v.1) _).mp hc)

theorem vertexAt_index {V R N hN} (C : CycleData V R N hN) (t : Fin N) :
    vertexAt C t.val=C.cycle t := by
  exact congrArg (fun v : V×Fin 4 => v.1) (interpret_index C t ⟨0,by decide⟩)

noncomputable def residualCycle {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (b : Bool) :
    CycleData (V×Fin 4) (ActualGrid R) (4*N) (by omega) :=
  if b then residualCycle1 cycles selected hn h2 hsym else residualCycle0 cycles selected hn h2 hsym

theorem residualCycle_ledger {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (b : Bool) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ q, SameEdge ((residualCycle cycles selected hn h2 hsym b).cycle q,
      (residualCycle cycles selected hn h2 hsym b).cycle (successor (show 0<4*N by omega) q)) e) ↔
    Occurs ((if b then R1Edges (normalizedMatching cycles selected hn) else
      R0Edges (normalizedMatching cycles selected hn)).map
        (fun g => (interpret (closeSelected (cycles 0) (selected 0)) g.1,
          interpret (closeSelected (cycles 0) (selected 0)) g.2))) e := by
  cases b
  · exact residual0_ledger cycles selected hn h2 hsym e
  · exact residual1_ledger cycles selected hn h2 hsym e

/-- Residual tours can use only parent0 horizontal edges and the selected
horizontal edge of another parent; all other horizontal parent edges are
excluded. This is derived from every actual residual cyclic edge. -/
theorem residual_horizontal_only {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (b : Bool) (u v : V) (row : Fin 4) (hne : u≠v)
    (hq : ∃ q, SameEdge ((residualCycle cycles selected hn h2 hsym b).cycle q,
      (residualCycle cycles selected hn h2 hsym b).cycle (successor (show 0<4*N by omega) q)) ((u,row),(v,row))) :
    (∃ t, SameEdge ((cycles 0).cycle t,(cycles 0).cycle (successor hN t)) (u,v)) ∨
    (∃ i : Fin k, SameEdge ((cycles i.succ).cycle (selected i.succ),
      (cycles i.succ).cycle (successor hN (selected i.succ))) (u,v)) := by
  let M := normalizedMatching cycles selected hn
  let C0 := closeSelected (cycles 0) (selected 0)
  obtain ⟨g,hg,hge⟩ := (residualCycle_ledger cycles selected hn h2 hsym b _).mp hq
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
  have he : SameEdge (vertexAt C0 f.1.1,vertexAt C0 f.2.1) (u,v) :=
    sameEdge_map (fun z : V×Fin 4 => z.1) hge
  rcases residualEdges_base M hN h2 b f hf with hh|⟨t,ht⟩|⟨i,hi⟩
  · rw [hh] at he
    rcases he with he|he <;> simp only [Prod.mk.injEq] at he
    all_goals exact False.elim (hne (by grind only))
  · have hp := sameEdge_map (vertexAt C0) ht
    simp only [vertexAt_index] at hp
    have hp := sameEdge_trans _ _ _ hp he
    left
    refine ⟨forward hN (successor hN (selected 0)) t,?_⟩
    have hr := rotate_step (cycles 0) (successor hN (selected 0)) t
    change SameEdge ((rotate (cycles 0) (successor hN (selected 0))).cycle t,
      (rotate (cycles 0) (successor hN (selected 0))).cycle (successor hN t)) _ at hp
    rw [hr] at hp
    exact hp
  · right
    have hp := sameEdge_map (vertexAt C0) hi
    have hp := sameEdge_trans _ _ _ hp he
    exact ⟨i,sameEdge_trans _ _ _
      (sameEdge_symm _ _ (normalized_selected_sameEdge cycles selected hn i)) hp⟩

/-- No actual horizontal host edge can occur both in either residual and
in any Ki. This is exact factor separation, using the old decomposition
ledger rather than an edge count. -/
theorem residual_other_horizontal_disjoint {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h2 : 2≤N) (b : Bool) (i : Fin k)
    (u v : V) (row : Fin 4) (hne : u≠v)
    (hr : ∃ q, SameEdge ((residualCycle d.cycles selected hn h2 d.symmetric b).cycle q,
      (residualCycle d.cycles selected hn h2 d.symmetric b).cycle (successor (show 0<4*N by omega) q))
      ((u,row),(v,row))) :
    ¬∃ p, SameEdge ((otherCycle d.cycles selected hn d.symmetric i).cycle p,
      (otherCycle d.cycles selected hn d.symmetric i).cycle (successor (show 0<4*N by omega) p))
      ((u,row),(v,row)) := by
  intro ho
  obtain ⟨p,hp⟩ := ho
  rcases residual_horizontal_only d.cycles selected hn h2 d.symmetric b u v row hne hr with
    ⟨t,ht⟩|⟨j,hj⟩
  · have hm := sameEdge_map (fun v : V => (v,row)) ht
    have he := sameEdge_trans _ _ _ hp (sameEdge_symm _ _ hm)
    have hf := ((other_horizontal_iff d selected hn i 0 t row).mp ⟨p,he⟩).1
    have hv := congrArg Fin.val hf
    simp at hv
  · have hm := sameEdge_map (fun v : V => (v,row)) hj
    have he := sameEdge_trans _ _ _ hp (sameEdge_symm _ _ hm)
    have ht := ((other_horizontal_iff d selected hn i j.succ (selected j.succ) row).mp ⟨p,he⟩).2
    exact ht rfl

#print axioms cyclic_position_unique
#print axioms block_ledger
#print axioms scan_local_labels_unique
#print axioms word_steps
#print axioms other_horizontal_iff
#print axioms other_vertical_iff
#print axioms other_vertical_unique
#print axioms other_edge_unique
#print axioms residual0_ledger
#print axioms residual1_ledger
#print axioms residual0_selected_cover
#print axioms residual1_selected_cover
#print axioms residual0_classes
#print axioms residual1_classes
#print axioms residual_other_horizontal_disjoint
end ErdePaths.HamiltonLedger
