import ErdePaths.HamiltonVerticalLabels
import ErdePaths.HamiltonRows
import ErdePaths.FiniteSaturation
import ErdePaths.HamiltonHost

namespace ErdePaths.HamiltonPartition
open HamiltonData HamiltonScan HamiltonNormalize HamiltonResidual HamiltonCycles HamiltonOtherCycles HamiltonLedger SquareLift

/-- Exact vertical scan ownership under any row transformation preserving the
base coordinate, covering both the original and reflected residual scan. -/
theorem scan_vertical_iff {N k} (M : Matching N k) (h2 : 2≤N)
    (F : Nat→Nat) (j a b : Nat) :
    ScanClasses M (fun v => (v.1,F v.2)) ((j,a),(j,b)) ↔
      j∈middle N ∧ ∃ p, HamiltonVerticalLabels.Class M (state M) j p ∧
        SameEdge (F (sRow p),F 3) (a,b) := by
  constructor
  · rintro (he|⟨q,hq,t,ht,he⟩|⟨q,hq,he⟩)
    · have hh := sameEdge_map (fun v : Nat×Nat => v.1) he
      rcases hh with hh|hh <;> simp only [Prod.mk.injEq] at hh <;> omega
    · cases t with
      | chord i r =>
        have hh := sameEdge_map (fun v : Nat×Nat => v.1) he
        have ho := M.ordered i
        rcases hh with hh|hh <;> simp only [labelEdge,Prod.mk.injEq] at hh <;> omega
      | vertical x p =>
        have hh := sameEdge_map (fun v : Nat×Nat => v.1) he
        have hx : x=j := by
          rcases hh with hh|hh <;> simp only [labelEdge,Prod.mk.injEq] at hh <;> omega
        subst x
        have hc := (HamiltonVerticalLabels.membership M (state M) j p).mp ⟨q,hq,ht⟩
        refine ⟨hc.1,p,hc.2,?_⟩
        exact sameEdge_map (fun v : Nat×Nat => v.2) he
    · have hh := sameEdge_map (fun v : Nat×Nat => v.1) he
      rcases hh with hh|hh <;> simp only [Prod.mk.injEq] at hh <;> omega
  · rintro ⟨hj,p,hp,he⟩
    obtain ⟨q,hq,ht⟩ := (HamiltonVerticalLabels.membership M (state M) j p).mpr ⟨hj,hp⟩
    exact Or.inr (Or.inl ⟨q,hq,.vertical j p,ht,
      sameEdge_map (fun r => (j,r)) he⟩)

def zeroVertical (c : Bool) (a b : Nat) : Prop :=
  if c then SameEdge (0,1) (a,b) ∨ SameEdge (2,3) (a,b)
  else SameEdge (0,2) (a,b) ∨ SameEdge (1,3) (a,b)

def lastVertical (s c : Bool) (a b : Nat) : Prop :=
  if c then SameEdge (1,3) (a,b) ∨ SameEdge (0,if s then 1 else 2) (a,b)
  else SameEdge (2,3) (a,b) ∨ SameEdge (0,if s then 2 else 1) (a,b)

theorem repairs_vertical_iff {N k} (M : Matching N k) (h2 : 2≤N) (c : Bool) (j a b : Nat) :
    Occurs (if c then R1Repairs M else R0Repairs M) ((j,a),(j,b)) ↔
      (j=0 ∧ zeroVertical c a b) ∨ (j=N-1 ∧ lastVertical (state M 0) c a b) := by
  have hn : N-1≠0 := by omega
  cases c <;> cases hs : state M 0 <;>
    simp only [R0Repairs,R1Repairs,zeroVertical,lastVertical,hs,Bool.false_eq_true,
      ite_false,ite_true,Occurs,List.mem_cons,List.not_mem_nil,or_false,
      or_and_right,exists_or,exists_eq_left,SameEdge,Prod.mk.injEq] <;> grind only

theorem openRows_not_vertical (N r j a b : Nat) :
    ¬Occurs (openRows N r) ((j,a),(j,b)) := by
  intro he
  obtain ⟨t,ht,he⟩ := (openRows_occurs N r _).mp he
  have hh := sameEdge_map (fun v : Nat×Nat => v.1) he
  rcases hh with hh|hh <;> simp only [Prod.mk.injEq] at hh <;> omega

def VerticalClass {N k} (M : Matching N k) (c : Bool) (j a b : Nat) : Prop :=
  (j=0 ∧ zeroVertical c a b) ∨
  (j=N-1 ∧ lastVertical (state M 0) c a b) ∨
  (j∈middle N ∧ ∃ p, HamiltonVerticalLabels.Class M (state M) j p ∧
    SameEdge ((if c then 3-sRow p else sRow p),(if c then 0 else 3)) (a,b))

/-- Exact vertical owner classification for both literal residuals. -/
theorem residual_vertical_coordinates {N k} (M : Matching N k) (h2 : 2≤N)
    (c : Bool) (j a b : Nat) :
    Occurs (if c then R1Edges M else R0Edges M) ((j,a),(j,b)) ↔ VerticalClass M c j a b := by
  have hi (l : List ((Nat×Nat)×(Nat×Nat))) :
      l.map (fun g => ((fun v : Nat×Nat => v) g.1,(fun v : Nat×Nat => v) g.2))=l := by
    simp
  cases c
  · simp only [Bool.false_eq_true,ite_false]
    have hh := R0_mapped_occurs M (fun v => v) ((j,a),(j,b))
    simp only [hi] at hh
    have hw : Occurs (WEdges M) ((j,a),(j,b)) ↔ ScanClasses M (fun v => v) ((j,a),(j,b)) := by
      simpa only [hi,ScanClasses] using W_mapped_occurs M (fun v => v) ((j,a),(j,b))
    rw [hh,hw]
    have hv := scan_vertical_iff M h2 (fun n => n) j a b
    change ScanClasses M (fun v => v) ((j,a),(j,b)) ↔ _ at hv
    change _ ↔ VerticalClass M false j a b
    rw [show Occurs (openRows N 0) ((j,a),(j,b)) ↔ False from iff_false_intro (openRows_not_vertical N 0 j a b)]
    change (False ∨ ScanClasses M (fun v => v) ((j,a),(j,b)) ∨ _) ↔ _
    have hr := repairs_vertical_iff M h2 false j a b
    simp only [Bool.false_eq_true,ite_false] at hr
    rw [hv,hr]
    simp only [VerticalClass,Bool.false_eq_true,ite_false]
    grind only
  · simp only [ite_true]
    have hh := R1_mapped_occurs M (fun v => v) ((j,a),(j,b))
    simp only [hi] at hh
    rw [hh]
    have hv := scan_vertical_iff M h2 (fun n => 3-n) j a b
    change ScanClasses M tau ((j,a),(j,b)) ↔ _ at hv
    have hw : Occurs ((WEdges M).map (fun g => (tau g.1,tau g.2))) ((j,a),(j,b)) ↔
        ScanClasses M tau ((j,a),(j,b)) := W_mapped_occurs M tau _
    rw [show Occurs (openRows N 3) ((j,a),(j,b)) ↔ False from iff_false_intro (openRows_not_vertical N 3 j a b)]
    have hr := repairs_vertical_iff M h2 true j a b
    simp only [ite_true] at hr
    rw [hw,hv,hr]
    simp only [VerticalClass,ite_true,show 3-3=0 by decide]
    grind only

def uninterpret {V R N hN} (C : CycleData V R N hN) (v : V×Fin 4) : Nat×Nat :=
  ((C.position v.1).val,v.2.val)

theorem uninterpret_interpret {V R N hN} (C : CycleData V R N hN) (v : Nat×Nat)
    (hv : v.1<N ∧ v.2<4) : uninterpret C (interpret C v)=v := by
  simp only [uninterpret,interpret,vertexAt,C.position_cycle]
  exact Prod.ext (Nat.mod_eq_of_lt hv.1) (Nat.mod_eq_of_lt hv.2)

theorem interpret_uninterpret {V R N hN} (C : CycleData V R N hN) (v : V×Fin 4) :
    interpret C (uninterpret C v)=v := by
  rw [uninterpret,interpret_index,C.cycle_position]

/-- Actual output edge occurrence is equivalent to the precise normalized
coordinate ledger. Box bounds are proved from the literal tours. -/
theorem residual_coordinates {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (c : Bool) (e : (V×Fin 4)×(V×Fin 4)) :
    (∃ q, SameEdge ((residualCycle cycles selected hn h2 hsym c).cycle q,
      (residualCycle cycles selected hn h2 hsym c).cycle (successor (show 0<4*N by omega) q)) e) ↔
    Occurs (if c then R1Edges (normalizedMatching cycles selected hn) else
      R0Edges (normalizedMatching cycles selected hn))
      (uninterpret (closeSelected (cycles 0) (selected 0)) e.1,
       uninterpret (closeSelected (cycles 0) (selected 0)) e.2) := by
  rw [residualCycle_ledger]
  let M := normalizedMatching cycles selected hn
  let C0 := closeSelected (cycles 0) (selected 0)
  constructor
  · rintro ⟨g,hg,hge⟩
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    have hb := residualEdges_bounds M h2 c f hf
    have hi := sameEdge_map (uninterpret C0) hge
    rw [uninterpret_interpret C0 f.1 hb.1,uninterpret_interpret C0 f.2 hb.2] at hi
    exact ⟨f,hf,hi⟩
  · intro he
    have hm := occurs_map_same (interpret C0) _ _ he
    simpa only [C0,interpret_uninterpret,Prod.eta] using hm

theorem residual_vertical_iff {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (c : Bool) (u : V) (a b : Fin 4) :
    (∃ q, SameEdge ((residualCycle cycles selected hn h2 hsym c).cycle q,
      (residualCycle cycles selected hn h2 hsym c).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) ↔
    VerticalClass (normalizedMatching cycles selected hn) c
      ((closeSelected (cycles 0) (selected 0)).position u).val a.val b.val := by
  rw [residual_coordinates]
  exact residual_vertical_coordinates (normalizedMatching cycles selected hn) h2 c _ _ _

theorem zero_disjoint (a b : Nat) : zeroVertical false a b→zeroVertical true a b→False := by
  simp only [zeroVertical,Bool.false_eq_true,ite_false,ite_true,SameEdge,Prod.mk.injEq]
  omega

theorem last_disjoint (s : Bool) (a b : Nat) : lastVertical s false a b→lastVertical s true a b→False := by
  cases s <;> simp only [lastVertical,Bool.false_eq_true,ite_false,ite_true,SameEdge,Prod.mk.injEq] <;> omega

theorem middle_disjoint (p q : Bool) (a b : Nat) :
    SameEdge (sRow p,3) (a,b)→SameEdge (3-sRow q,0) (a,b)→False := by
  cases p <;> cases q <;>
    simp only [sRow,rowNat,rowIndex,SameEdge,Prod.mk.injEq] <;> omega

/-- The two residuals have no common vertical edge in any coordinate. -/
theorem vertical_classes_disjoint {N k} (M : Matching N k) (h2 : 2≤N) (j a b : Nat)
    (h0 : VerticalClass M false j a b) (h1 : VerticalClass M true j a b) : False := by
  have hn : N-1≠0 := by omega
  simp only [VerticalClass,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  rcases h0 with ⟨hz,h0⟩|⟨hl,h0⟩|⟨hm,p,hp,h0⟩
  · rcases h1 with ⟨hz',h1⟩|⟨hl',h1⟩|⟨hm',q,hq,h1⟩
    · exact zero_disjoint a b h0 h1
    · omega
    · have hh := middle_mem.mp hm'; omega
  · rcases h1 with ⟨hz',h1⟩|⟨hl',h1⟩|⟨hm',q,hq,h1⟩
    · omega
    · exact last_disjoint (state M 0) a b h0 h1
    · have hh := middle_mem.mp hm'; omega
  · rcases h1 with ⟨hz',h1⟩|⟨hl',h1⟩|⟨hm',q,hq,h1⟩
    · have hh := middle_mem.mp hm; omega
    · have hh := middle_mem.mp hm; omega
    · exact middle_disjoint p q a b h0 h1

theorem residual_vertical_disjoint {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (u : V) (a b : Fin 4)
    (h0 : ∃ q, SameEdge ((residualCycle0 cycles selected hn h2 hsym).cycle q,
      (residualCycle0 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b)))
    (h1 : ∃ q, SameEdge ((residualCycle1 cycles selected hn h2 hsym).cycle q,
      (residualCycle1 cycles selected hn h2 hsym).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) : False :=
  vertical_classes_disjoint _ h2 _ _ _
    ((residual_vertical_iff cycles selected hn h2 hsym false u a b).mp h0)
    ((residual_vertical_iff cycles selected hn h2 hsym true u a b).mp h1)

theorem vertical_lower_iff {N k} (M : Matching N k) (c : Bool) (i : Fin k) (a b : Nat) :
    VerticalClass M c (M.lower i) a b ↔
      SameEdge ((if c then 3-sRow (state M (M.upper i)) else sRow (state M (M.upper i))),
        (if c then 0 else 3)) (a,b) := by
  have hlo := M.lower_pos i
  have ho := M.ordered i
  have hu := M.upper_bound i
  have hz : M.lower i≠0 := by omega
  have hl : M.lower i≠N-1 := by omega
  have hc : ∀p, HamiltonVerticalLabels.Class M (state M) (M.lower i) p ↔ p=state M (M.upper i) := by
    intro p
    simp [HamiltonVerticalLabels.Class,M.lower_kind]
  simp only [VerticalClass,hz,hl,false_and,false_or,lower_middle,hc,true_and,exists_eq_left]

theorem vertical_upper_iff {N k} (M : Matching N k) (c : Bool) (i : Fin k) (a b : Nat) :
    VerticalClass M c (M.upper i) a b ↔
      SameEdge ((if c then 3-sRow (!(state M (M.upper i))) else sRow (!(state M (M.upper i)))),
        (if c then 0 else 3)) (a,b) := by
  have hlo := M.lower_pos i
  have ho := M.ordered i
  have hu := M.upper_bound i
  have hz : M.upper i≠0 := by omega
  have hl : M.upper i≠N-1 := by omega
  have hm : M.upper i∈middle N := (middle_mem).mpr ⟨by omega,hu⟩
  have hc : ∀p, HamiltonVerticalLabels.Class M (state M) (M.upper i) p ↔ p=!(state M (M.upper i)) := by
    intro p
    simp [HamiltonVerticalLabels.Class,M.upper_kind]
  simp only [VerticalClass,hz,hl,false_and,false_or,hm,hc,true_and,exists_eq_left]

theorem lower_rows_disjoint (c s : Bool) (a b : Nat)
    (hr : SameEdge ((if c then 3-sRow s else sRow s),(if c then 0 else 3)) (a,b))
    (hk : SameEdge (oRow s,3) (a,b) ∨ SameEdge (sRow s,0) (a,b)) : False := by
  cases c <;> cases s <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,sRow,oRow,rowNat,rowIndex,
      Bool.not_false,Bool.not_true,SameEdge,Prod.mk.injEq] at hr hk <;> omega

theorem upper_rows_disjoint (c s : Bool) (a b : Nat)
    (hr : SameEdge ((if c then 3-sRow (!s) else sRow (!s)),(if c then 0 else 3)) (a,b))
    (hk : SameEdge (0,oRow s) (a,b) ∨ SameEdge (3,sRow s) (a,b)) : False := by
  cases c <;> cases s <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,sRow,oRow,rowNat,rowIndex,
      Bool.not_false,Bool.not_true,SameEdge,Prod.mk.injEq] at hr hk <;> omega

theorem position_vertexAt {V R N hN} (C : CycleData V R N hN) (j : Nat) (hj : j<N) :
    (C.position (vertexAt C j)).val=j := by
  simp only [vertexAt,C.position_cycle,Nat.mod_eq_of_lt hj]

/-- Both residuals are disjoint from every Ki on all actual vertical edges. -/
theorem residual_other_vertical_disjoint {V R k N hN}
    (cycles : Fin (k+1)→CycleData V R N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList cycles selected).Nodup) (h2 : 2≤N)
    (hsym : ∀u v, R u v→R v u) (c : Bool) (i : Fin k) (u : V) (a b : Fin 4)
    (hr : ∃ q, SameEdge ((residualCycle cycles selected hn h2 hsym c).cycle q,
      (residualCycle cycles selected hn h2 hsym c).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b)))
    (hk : ∃ q, SameEdge ((otherCycle cycles selected hn hsym i).cycle q,
      (otherCycle cycles selected hn hsym i).cycle (successor (show 0<4*N by omega) q)) ((u,a),(u,b))) : False := by
  let M := normalizedMatching cycles selected hn
  let C0 := closeSelected (cycles 0) (selected 0)
  have hr' := (residual_vertical_iff cycles selected hn h2 hsym c u a b).mp hr
  have hk' := (other_vertical_iff cycles selected hn hsym i u a b).mp hk
  rcases hk' with ⟨hu,hk'⟩|⟨hu,hk'⟩
  · rw [hu,position_vertexAt C0 (M.lower i) (endpointPosition_bound M i false)] at hr'
    have hr' := (vertical_lower_iff M c i a.val b.val).mp hr'
    apply lower_rows_disjoint c (state M (M.upper i)) a.val b.val hr'
    rcases hk' with hk'|hk'
    · exact Or.inr (sameEdge_map (fun r : Fin 4 => r.val) hk')
    · exact Or.inl (sameEdge_map (fun r : Fin 4 => r.val) hk')
  · rw [hu,position_vertexAt C0 (M.upper i) (endpointPosition_bound M i true)] at hr'
    have hr' := (vertical_upper_iff M c i a.val b.val).mp hr'
    apply upper_rows_disjoint c (state M (M.upper i)) a.val b.val hr'
    rcases hk' with hk'|hk'
    · exact Or.inl (sameEdge_map (fun r : Fin 4 => r.val) hk')
    · exact Or.inr (sameEdge_map (fun r : Fin 4 => r.val) hk')

/-- A chord label can occur only in its lower block and the two allocated rows. -/
theorem chord_membership {N k} (M : Matching N k) (j : Nat) (i : Fin k) (r : Row)
    (hm : (.chord i r : Label k)∈labels M (state M) j) :
    j=M.lower i ∧ (r=.top ∨ r=.primary (!(state M (M.upper i)))) := by
  cases hk : M.kind j with
  | ordinary => simp [labels,hk] at hm
  | upper t => simp [labels,hk] at hm
  | lower t =>
    have hj := M.kind_lower j t hk
    simp [labels,hk] at hm
    rcases hm with ⟨hi,hr⟩|⟨hi,hr⟩
    · subst t; exact ⟨hj,Or.inl hr⟩
    · subst t; exact ⟨hj,Or.inr hr⟩

/-- Every horizontal scan edge is either the indexed parent bridge or one
of the two specified selected-chord rows. The row map includes reflection. -/
theorem scan_horizontal_only {N k} (M : Matching N k) (h2 : 2≤N)
    (F : Nat→Nat) (x y r : Nat) (hne : x≠y)
    (he : ScanClasses M (fun v => (v.1,F v.2)) ((x,r),(y,r))) :
    (∃ t, t+1<N ∧ SameEdge (t,t+1) (x,y) ∧ r=F (sRow (state M t))) ∨
    (∃ i, SameEdge (M.lower i,M.upper i) (x,y) ∧
      (r=F 3 ∨ r=F (oRow (state M (M.upper i))))) := by
  rcases he with he|⟨j,hj,a,ha,he⟩|⟨j,hj,he⟩
  · left
    refine ⟨N-2,by omega,?_,?_⟩
    · have hb := sameEdge_map (fun v : Nat×Nat=>v.1) he
      have hn : N-2+1=N-1 := by omega
      rw [hn]
      exact sameEdge_trans _ _ _ (Or.inr rfl) hb
    · have hr := sameEdge_map (fun v : Nat×Nat=>v.2) he
      simp only [SameEdge,Prod.mk.injEq] at hr
      rw [state_initial]
      simp only [sRow,rowNat,rowIndex]
      grind only
  · cases a with
    | chord i row =>
      have hc := chord_membership M j i row ha
      right
      refine ⟨i,sameEdge_map (fun v : Nat×Nat=>v.1) he,?_⟩
      have hr := sameEdge_map (fun v : Nat×Nat=>v.2) he
      simp only [labelEdge,SameEdge,Prod.mk.injEq] at hr
      rcases hc.2 with hrow|hrow
      · subst row; left; simp only [rowNat,rowIndex] at hr; grind only
      · subst row; right; change r=F (rowNat (.primary (!(state M (M.upper i)))))
        grind only
    | vertical v b =>
      have hb := sameEdge_map (fun v : Nat×Nat=>v.1) he
      simp only [labelEdge,SameEdge,Prod.mk.injEq] at hb
      exact False.elim (hne (by grind only))
  · left
    refine ⟨j,by omega,?_,?_⟩
    · exact sameEdge_trans _ _ _ (Or.inr rfl) (sameEdge_map (fun v : Nat×Nat=>v.1) he)
    · have hr := sameEdge_map (fun v : Nat×Nat=>v.2) he
      simp only [SameEdge,Prod.mk.injEq] at hr
      grind only

def closingRow {N k} (M : Matching N k) (c : Bool) (r : Nat) : Prop :=
  r=(if c then 0 else 3) ∨ r=(if c then sRow (state M 0) else oRow (state M 0))

theorem repairs_horizontal_iff {N k} (M : Matching N k) (_h2 : 2≤N)
    (c : Bool) (x y r : Nat) (hne : x≠y) :
    Occurs (if c then R1Repairs M else R0Repairs M) ((x,r),(y,r)) ↔
    SameEdge (0,N-1) (x,y) ∧ closingRow M c r := by
  cases c <;> cases hs : state M 0 <;>
    simp only [R0Repairs,R1Repairs,closingRow,hs,Bool.false_eq_true,
      ite_false,ite_true,Occurs,List.mem_cons,List.not_mem_nil,or_false,
      or_and_right,exists_or,exists_eq_left,sRow,oRow,rowNat,rowIndex,
      Bool.not_false,Bool.not_true,SameEdge,Prod.mk.injEq] <;> grind only

def HorizontalClass {N k} (M : Matching N k) (c : Bool) (x y r : Nat) : Prop :=
  (∃t, t+1<N ∧ SameEdge (t,t+1) (x,y) ∧
    (r=(if c then 3 else 0) ∨ r=(if c then 3-sRow (state M t) else sRow (state M t)))) ∨
  (SameEdge (0,N-1) (x,y) ∧ closingRow M c r) ∨
  (∃i, SameEdge (M.lower i,M.upper i) (x,y) ∧
    (r=(if c then 0 else 3) ∨
     r=(if c then 3-oRow (state M (M.upper i)) else oRow (state M (M.upper i)))))

/-- Complete horizontal possibilities, including the actual incoming scan
state at every parent bridge and the exact two selected-chord rows. -/
theorem residual_horizontal_coordinates {N k} (M : Matching N k) (h2 : 2≤N)
    (c : Bool) (x y r : Nat) (hne : x≠y)
    (he : Occurs (if c then R1Edges M else R0Edges M) ((x,r),(y,r))) :
    HorizontalClass M c x y r := by
  have hi (l : List ((Nat×Nat)×(Nat×Nat))) :
      l.map (fun g => ((fun v : Nat×Nat => v) g.1,(fun v : Nat×Nat => v) g.2))=l := by simp
  cases c
  · simp only [Bool.false_eq_true,ite_false] at he
    have hh := R0_mapped_occurs M (fun v=>v) ((x,r),(y,r))
    simp only [hi] at hh
    have hw : Occurs (WEdges M) ((x,r),(y,r)) ↔ ScanClasses M (fun v=>v) ((x,r),(y,r)) := by
      simpa only [hi,ScanClasses] using W_mapped_occurs M (fun v=>v) ((x,r),(y,r))
    rcases hh.mp he with he|he|he
    · obtain ⟨t,ht,hg⟩ := (openRows_occurs N 0 _).mp he
      have hb := sameEdge_map (fun v : Nat×Nat=>v.1) hg
      have hr := sameEdge_map (fun v : Nat×Nat=>v.2) hg
      have hr : r=0 := by simp only [SameEdge,Prod.mk.injEq] at hr; grind only
      exact Or.inl ⟨t,ht,hb,Or.inl hr⟩
    · have hs := scan_horizontal_only M h2 (fun n=>n) x y r hne (hw.mp he)
      rcases hs with ⟨t,ht,hb,hr⟩|⟨i,hb,hr⟩
      · exact Or.inl ⟨t,ht,hb,Or.inr hr⟩
      · exact Or.inr (Or.inr ⟨i,hb,hr⟩)
    · exact Or.inr (Or.inl ((repairs_horizontal_iff M h2 false x y r hne).mp he))
  · simp only [ite_true] at he
    have hh := R1_mapped_occurs M (fun v=>v) ((x,r),(y,r))
    simp only [hi] at hh
    rcases hh.mp he with he|he|he
    · obtain ⟨t,ht,hg⟩ := (openRows_occurs N 3 _).mp he
      have hb := sameEdge_map (fun v : Nat×Nat=>v.1) hg
      have hr := sameEdge_map (fun v : Nat×Nat=>v.2) hg
      have hr : r=3 := by simp only [SameEdge,Prod.mk.injEq] at hr; grind only
      exact Or.inl ⟨t,ht,hb,Or.inl hr⟩
    · have hw := W_mapped_occurs M tau ((x,r),(y,r))
      have hs := scan_horizontal_only M h2 (fun n=>3-n) x y r hne (hw.mp he)
      rcases hs with ⟨t,ht,hb,hr⟩|⟨i,hb,hr⟩
      · exact Or.inl ⟨t,ht,hb,Or.inr hr⟩
      · exact Or.inr (Or.inr ⟨i,hb,hr⟩)
    · exact Or.inr (Or.inl ((repairs_horizontal_iff M h2 true x y r hne).mp he))

theorem bridge_rows_disjoint (s : Bool) (r : Nat)
    (h0 : r=0 ∨ r=sRow s) (h1 : r=3 ∨ r=3-sRow s) : False := by
  cases s <;> simp only [sRow,rowNat,rowIndex] at h0 h1 <;> omega

theorem closing_rows_disjoint {N k} (M : Matching N k) (r : Nat)
    (h0 : closingRow M false r) (h1 : closingRow M true r) : False := by
  cases hs : state M 0 <;>
    simp only [closingRow,hs,Bool.false_eq_true,ite_false,ite_true,
      sRow,oRow,rowNat,rowIndex,Bool.not_false,Bool.not_true] at h0 h1 <;> omega

theorem chord_rows_disjoint (s : Bool) (r : Nat)
    (h0 : r=3 ∨ r=oRow s) (h1 : r=0 ∨ r=3-oRow s) : False := by
  cases s <;> simp only [oRow,rowNat,rowIndex,Bool.not_false,Bool.not_true] at h0 h1 <;> omega

theorem chord_index_unique {N k} (M : Matching N k) (i j : Fin k)
    (he : SameEdge (M.lower i,M.upper i) (M.lower j,M.upper j)) : i=j := by
  have hi := M.ordered i
  have hj := M.ordered j
  have hlo : M.lower i=M.lower j := by
    rcases he with he|he <;> simp only [Prod.mk.injEq] at he <;> omega
  have hk := congrArg M.kind hlo
  rw [M.lower_kind i,M.lower_kind j] at hk
  exact Kind.lower.inj hk

theorem nonclosing_position {N} (hN : 0<N) (t : Nat) (ht : t+1<N) :
    PositionEdge hN t (t+1) := by
  refine ⟨⟨t,by omega⟩,?_⟩
  have hs : (successor hN ⟨t,by omega⟩).val=t+1 := by
    simp only [successor,Nat.mod_eq_of_lt ht]
  simp only [hs,SameEdge]; exact Or.inl trivial

theorem closing_position {N} (hN : 0<N) : PositionEdge hN 0 (N-1) := by
  refine ⟨⟨N-1,by omega⟩,Or.inr ?_⟩
  have hs : (successor hN ⟨N-1,by omega⟩).val=0 := by
    simp only [successor]; have hh : N-1+1=N := by omega
    rw [hh,Nat.mod_self]
  simp only [hs]

/-- Numeric residual horizontal separation follows from the genuine old
factor separation: selected chords are not parent-zero cyclic edges. -/
theorem horizontal_classes_disjoint {N k} (hN : 0<N) (h3 : 3≤N) (M : Matching N k)
    (hsep : ∀i, ¬PositionEdge hN (M.lower i) (M.upper i))
    (x y r : Nat) (h0 : HorizontalClass M false x y r)
    (h1 : HorizontalClass M true x y r) : False := by
  simp only [HorizontalClass,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  rcases h0 with ⟨t,ht,hb,hrow⟩|⟨hb,hrow⟩|⟨i,hb,hrow⟩
  · rcases h1 with ⟨q,hq,hb',hrow'⟩|⟨hb',hrow'⟩|⟨i,hb',hrow'⟩
    · have he := sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb')
      have hq' : t=q := by rcases he with he|he <;> simp only [Prod.mk.injEq] at he <;> omega
      subst q
      exact bridge_rows_disjoint _ _ hrow hrow'
    · have he := sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb')
      rcases he with he|he <;> simp only [Prod.mk.injEq] at he <;> omega
    · apply hsep i
      obtain ⟨p,hp⟩ := nonclosing_position hN t ht
      exact ⟨p,sameEdge_trans _ _ _ hp (sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb'))⟩
  · rcases h1 with ⟨q,hq,hb',hrow'⟩|⟨hb',hrow'⟩|⟨i,hb',hrow'⟩
    · have he := sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb')
      rcases he with he|he <;> simp only [Prod.mk.injEq] at he <;> omega
    · exact closing_rows_disjoint M r hrow hrow'
    · apply hsep i
      obtain ⟨p,hp⟩ := closing_position hN
      exact ⟨p,sameEdge_trans _ _ _ hp (sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb'))⟩
  · rcases h1 with ⟨q,hq,hb',hrow'⟩|⟨hb',hrow'⟩|⟨j,hb',hrow'⟩
    · apply hsep i
      obtain ⟨p,hp⟩ := nonclosing_position hN q hq
      exact ⟨p,sameEdge_trans _ _ _ hp (sameEdge_trans _ _ _ hb' (sameEdge_symm _ _ hb))⟩
    · apply hsep i
      obtain ⟨p,hp⟩ := closing_position hN
      exact ⟨p,sameEdge_trans _ _ _ hp (sameEdge_trans _ _ _ hb' (sameEdge_symm _ _ hb))⟩
    · have hij := chord_index_unique M i j (sameEdge_trans _ _ _ hb (sameEdge_symm _ _ hb'))
      subst j
      exact chord_rows_disjoint _ _ hrow hrow'

/-- This supplies the classifier's exclusion from actual input factor
ownership, not as a new existence or geometric hypothesis. -/
theorem normalized_chords_not_position {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) :
    ∀i, ¬PositionEdge hN ((normalizedMatching d.cycles selected hn).lower i)
      ((normalizedMatching d.cycles selected hn).upper i) := by
  intro i he
  obtain ⟨t,ht⟩ := he
  have hp := sameEdge_map (vertexAt (closeSelected (d.cycles 0) (selected 0))) ht
  have hp := sameEdge_symm _ _ hp
  simp only [vertexAt_index] at hp
  exact selected_not_base d selected hn i t hp

/-- The two genuine residual cycles have no common horizontal edge. -/
theorem residual_horizontal_disjoint {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (u v : V) (row : Fin 4) (hne : u≠v)
    (h0 : ∃q, SameEdge ((residualCycle0 d.cycles selected hn (by omega) d.symmetric).cycle q,
      (residualCycle0 d.cycles selected hn (by omega) d.symmetric).cycle
      (successor (show 0<4*N by omega) q)) ((u,row),(v,row)))
    (h1 : ∃q, SameEdge ((residualCycle1 d.cycles selected hn (by omega) d.symmetric).cycle q,
      (residualCycle1 d.cycles selected hn (by omega) d.symmetric).cycle
      (successor (show 0<4*N by omega) q)) ((u,row),(v,row))) : False := by
  let C0 := closeSelected (d.cycles 0) (selected 0)
  let M := normalizedMatching d.cycles selected hn
  have hne' : (C0.position u).val≠(C0.position v).val := by
    intro hh
    have hh' : C0.position u=C0.position v := Fin.ext hh
    apply hne
    calc u = C0.cycle (C0.position u) := (C0.cycle_position u).symm
         _ = C0.cycle (C0.position v) := congrArg C0.cycle hh'
         _ = v := C0.cycle_position v
  have h0' := (residual_coordinates d.cycles selected hn (by omega) d.symmetric false _).mp h0
  have h1' := (residual_coordinates d.cycles selected hn (by omega) d.symmetric true _).mp h1
  apply horizontal_classes_disjoint hN h3 M (normalized_chords_not_position d selected hn)
    (C0.position u).val (C0.position v).val row.val
  · exact residual_horizontal_coordinates M (by omega) false _ _ _ hne' h0'
  · exact residual_horizontal_coordinates M (by omega) true _ _ _ hne' h1'

def CyclicOccurs {V R N hN} (C : CycleData V R N hN) (e : V×V) : Prop :=
  ∃q, SameEdge (C.cycle q,C.cycle (successor hN q)) e

theorem residual_mutual_disjoint {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (x y : V×Fin 4) (ha : ActualGrid R x y)
    (h0 : CyclicOccurs (residualCycle0 d.cycles selected hn (by omega) d.symmetric) (x,y))
    (h1 : CyclicOccurs (residualCycle1 d.cycles selected hn (by omega) d.symmetric) (x,y)) : False := by
  rcases ha with ⟨hb,hr⟩|⟨hr,hb⟩
  · have hx : ((x.1,x.2),(x.1,y.2))=(x,y) := by
      apply Prod.ext
      · rfl
      · exact Prod.ext hb rfl
    rw [←hx] at h0 h1
    exact residual_vertical_disjoint d.cycles selected hn (by omega) d.symmetric _ _ _ h0 h1
  · have hx : ((x.1,x.2),(y.1,x.2))=(x,y) := by
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl hr
    rw [←hx] at h0 h1
    have hne : x.1≠y.1 := by intro he; rw [he] at hb; exact d.loopfree _ hb
    exact residual_horizontal_disjoint d selected hn h3 _ _ _ hne h0 h1

theorem residual_other_disjoint {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N) (c : Bool) (i : Fin k)
    (x y : V×Fin 4) (ha : ActualGrid R x y)
    (hr : CyclicOccurs (residualCycle d.cycles selected hn (by omega) d.symmetric c) (x,y))
    (hk : CyclicOccurs (otherCycle d.cycles selected hn d.symmetric i) (x,y)) : False := by
  rcases ha with ⟨hb,ha⟩|⟨ha,hb⟩
  · have hx : ((x.1,x.2),(x.1,y.2))=(x,y) := by
      apply Prod.ext
      · rfl
      · exact Prod.ext hb rfl
    rw [←hx] at hr hk
    exact residual_other_vertical_disjoint d.cycles selected hn (by omega) d.symmetric c i _ _ _ hr hk
  · have hx : ((x.1,x.2),(y.1,x.2))=(x,y) := by
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl ha
    rw [←hx] at hr hk
    have hne : x.1≠y.1 := by intro he; rw [he] at hb; exact d.loopfree _ hb
    obtain ⟨q,hq⟩ := hk
    exact residual_other_horizontal_disjoint d selected hn (by omega) c i _ _ _ hne hr ⟨q,hq⟩

noncomputable def combinedCycle {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N) :
    Sum Bool (Fin k)→CycleData (V×Fin 4) (ActualGrid R) (4*N) (by omega)
  | .inl c => residualCycle d.cycles selected hn (by omega) d.symmetric c
  | .inr i => otherCycle d.cycles selected hn d.symmetric i

/-- Genuine global cyclic-edge injection for the entire constructed family.
This precedes and justifies any subsequent finite saturation argument. -/
theorem combined_unique {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (i j : Sum Bool (Fin k)) (q p : Fin (4*N))
    (he : SameEdge ((combinedCycle d selected hn h3 i).cycle q,
      (combinedCycle d selected hn h3 i).cycle (successor (show 0<4*N by omega) q))
      ((combinedCycle d selected hn h3 j).cycle p,
      (combinedCycle d selected hn h3 j).cycle (successor (show 0<4*N by omega) p))) :
    i=j ∧ q=p := by
  let x := (combinedCycle d selected hn h3 i).cycle q
  let y := (combinedCycle d selected hn h3 i).cycle (successor (show 0<4*N by omega) q)
  have hi : CyclicOccurs (combinedCycle d selected hn h3 i) (x,y) := ⟨q,Or.inl rfl⟩
  have hj : CyclicOccurs (combinedCycle d selected hn h3 j) (x,y) := ⟨p,sameEdge_symm _ _ he⟩
  have ha : ActualGrid R x y := (combinedCycle d selected hn h3 i).adjacent q
  have hij : i=j := by
    cases i with
    | inl b => cases j with
      | inl c =>
        cases b <;> cases c
        · rfl
        · exact False.elim (residual_mutual_disjoint d selected hn h3 x y ha hi hj)
        · exact False.elim (residual_mutual_disjoint d selected hn h3 x y ha hj hi)
        · rfl
      | inr j => exact False.elim (residual_other_disjoint d selected hn h3 b j x y ha hi hj)
    | inr i => cases j with
      | inl b => exact False.elim (residual_other_disjoint d selected hn h3 b i x y ha hj hi)
      | inr j =>
        have hh := other_edge_unique d selected hn i j q p he
        exact congrArg Sum.inr hh.1
  subst j
  exact ⟨rfl,cyclic_position_unique (combinedCycle d selected hn h3 i) (by omega) q p he⟩

def factorList (k : Nat) : List (Sum Bool (Fin k)) :=
  [.inl false,.inl true]++(List.finRange k).map Sum.inr

theorem factorList_length (k : Nat) : (factorList k).length=k+2 := by simp only [factorList,List.length_append,List.length_cons,List.length_nil,List.length_map,List.length_finRange]; omega

theorem factorList_full {k} (i : Sum Bool (Fin k)) : i∈factorList k := by
  cases i with
  | inl b => cases b <;> simp [factorList]
  | inr i => simp [factorList]

theorem factorList_nodup (k : Nat) : (factorList k).Nodup := by
  have hn : ((List.finRange k).map (Sum.inr : Fin k→Sum Bool (Fin k))).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange k).imp
    intro a b hab he
    exact hab (Sum.inr.inj he)
  simpa [factorList,List.nodup_cons] using hn

def slots (k N : Nat) : List (Sum Bool (Fin k)×Fin (4*N)) :=
  (factorList k).flatMap (fun i=>(List.finRange (4*N)).map (fun q=>(i,q)))

theorem slots_nodup (k N : Nat) : (slots k N).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange (4*N)).imp
    intro a b hab he
    exact hab (Prod.mk.inj he).2
  · apply (factorList_nodup k).imp
    intro i j hij a ha b hb he
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
    exact hij (Prod.mk.inj he).1

theorem slots_full {k N} (i : Sum Bool (Fin k)) (q : Fin (4*N)) : (i,q)∈slots k N := by
  apply List.mem_flatMap.mpr
  exact ⟨i,factorList_full i,List.mem_map.mpr ⟨q,List.mem_finRange q,rfl⟩⟩

theorem slots_length (k N : Nat) : (slots k N).length=(k+2)*(4*N) := by
  unfold slots
  rw [List.length_flatMap]
  simp only [List.length_map,List.length_finRange]
  have hh : ∀l : List (Sum Bool (Fin k)), (l.map (fun _=>4*N)).sum=l.length*(4*N) := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]; omega
  rw [hh,factorList_length]

noncomputable def slotEdge {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (a : Sum Bool (Fin k)×Fin (4*N)) : (V×Fin 4)×(V×Fin 4) :=
  ((combinedCycle d selected hn h3 a.1).cycle a.2,
   (combinedCycle d selected hn h3 a.1).cycle (successor (by omega) a.2))

noncomputable def slotHost {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (a : Sum Bool (Fin k)×Fin (4*N)) : HamiltonHost.Host (k+1) N :=
  Classical.choose (HamiltonHost.cover d (d.cycles 0).toClockData
    (slotEdge d selected hn h3 a).1 (slotEdge d selected hn h3 a).2
    ((combinedCycle d selected hn h3 a.1).adjacent a.2))

theorem slotHost_edge {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (a : Sum Bool (Fin k)×Fin (4*N)) :
    SameEdge (HamiltonHost.decode d (d.cycles 0).toClockData (slotHost d selected hn h3 a))
      (slotEdge d selected hn h3 a) :=
  Classical.choose_spec (HamiltonHost.cover d (d.cycles 0).toClockData
    (slotEdge d selected hn h3 a).1 (slotEdge d selected hn h3 a).2
    ((combinedCycle d selected hn h3 a.1).adjacent a.2))

theorem slotHost_injective {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N) :
    Function.Injective (slotHost d selected hn h3) := by
  intro a b he
  have ha := slotHost_edge d selected hn h3 a
  have hb := slotHost_edge d selected hn h3 b
  rw [he] at ha
  have hh := combined_unique d selected hn h3 a.1 b.1 a.2 b.2
    (sameEdge_trans _ _ _ (sameEdge_symm _ _ ha) hb)
  exact Prod.ext hh.1 hh.2

/-- Saturation of the explicit actual host carrier supplies full coverage,
after the independently proved global physical edge injection. -/
theorem combined_cover {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N)
    (x y : V×Fin 4) (ha : ActualGrid R x y) :
    ∃ i q, SameEdge ((combinedCycle d selected hn h3 i).cycle q,
      (combinedCycle d selected hn h3 i).cycle (successor (show 0<4*N by omega) q)) (x,y) := by
  let f := slotHost d selected hn h3
  have hi : ((slots k N).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply (slots_nodup k N).imp
    intro a b hab he
    exact hab (slotHost_injective d selected hn h3 he)
  have hs : (slots k N).map f ⊆ HamiltonHost.all (k+1) N := by
    intro a _; exact HamiltonHost.mem_all a
  have hl : (HamiltonHost.all (k+1) N).length≤((slots k N).map f).length := by
    rw [List.length_map,slots_length,HamiltonHost.length_all]
    have hk : (k+1)+1=k+2 := by omega
    rw [hk,Nat.mul_comm (k+2) (4*N)]
    exact Nat.le_refl _
  have hc := FiniteSaturation.list_full hi hs hl
  obtain ⟨a,ha⟩ := HamiltonHost.cover d (d.cycles 0).toClockData x y ha
  obtain ⟨b,hb,he⟩ := List.mem_map.mp (hc (HamiltonHost.mem_all a))
  have hh := slotHost_edge d selected hn h3 b
  change f b=a at he
  change SameEdge (HamiltonHost.decode d (d.cycles 0).toClockData (f b)) _ at hh
  rw [he] at hh
  exact ⟨b.1,b.2,sameEdge_trans _ _ _ (sameEdge_symm _ _ hh) ha⟩

def factorAt {k : Nat} (i : Fin (k+2)) : Sum Bool (Fin k) :=
  (factorList k)[i.val]'(by rw [factorList_length]; exact i.isLt)

theorem factorAt_injective {k : Nat} : Function.Injective (@factorAt k) := by
  intro i j he
  apply Fin.ext
  exact (factorList_nodup k).eq_of_getElem_eq _ _ he

theorem factorAt_surjective {k : Nat} : Function.Surjective (@factorAt k) := by
  intro a
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (factorList_full a)
  have hb : i<k+2 := by rw [←factorList_length]; exact hi
  exact ⟨⟨i,hb⟩,he⟩

/-- Uniform constructive Hamilton decomposition of the actual C4 product.
All output cycles, adjacency, coverage, and undirected unique ownership
are proved from the input decomposition and selected disjoint endpoints. -/
noncomputable def product {V R k N hN}
    (d : DecompositionData V R (k+1) N hN) (selected : Fin (k+1)→Fin N)
    (hn : (endpointList d.cycles selected).Nodup) (h3 : 3≤N) :
    DecompositionData (V×Fin 4) (ActualGrid R) (k+2) (4*N) (by omega) where
  cycles i := combinedCycle d selected hn h3 (factorAt i)
  symmetric x y h := by
    rcases h with ⟨hb,hr⟩|⟨hr,hb⟩
    · exact Or.inl ⟨hb.symm,adjacent_symm hr⟩
    · exact Or.inr ⟨hr.symm,d.symmetric _ _ hb⟩
  loopfree x h := by
    rcases h with ⟨_,hr⟩|⟨_,hb⟩
    · exact adjacent_ne hr rfl
    · exact d.loopfree _ hb
  cover x y h := by
    obtain ⟨i,q,hq⟩ := combined_cover d selected hn h3 x y h
    obtain ⟨j,hj⟩ := factorAt_surjective i
    exact ⟨j,q,hj ▸ hq⟩
  unique i q j p h := by
    have hh := combined_unique d selected hn h3 (factorAt i) (factorAt j) q p h
    exact ⟨factorAt_injective hh.1,hh.2⟩

#print axioms scan_vertical_iff
#print axioms residual_vertical_coordinates
#print axioms residual_vertical_disjoint
#print axioms residual_other_vertical_disjoint
#print axioms residual_horizontal_disjoint
#print axioms combined_unique
#print axioms slots_nodup
#print axioms combined_cover
#print axioms product
end ErdePaths.HamiltonPartition
