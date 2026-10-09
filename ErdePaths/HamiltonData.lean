import ErdePaths.SourceClock

namespace ErdePaths.HamiltonData
open SquareLift

/-- An actual spanning cyclic tour, with both inverse laws and actual edges. -/
structure CycleData (V : Type) (R : V → V → Prop) (N : Nat) (hN : 0<N)
    extends SourceClock.ClockData V N where
  adjacent : ∀ t, R (cycle t) (cycle (successor hN t))

/-- Faithful Hamilton factors: every undirected host edge has one factor and
one cyclic edge position. No output decomposition existence is an input. -/
structure DecompositionData (V : Type) (R : V → V → Prop)
    (m N : Nat) (hN : 0<N) where
  cycles : Fin m → CycleData V R N hN
  symmetric : ∀ u v, R u v → R v u
  loopfree : ∀ u, ¬ R u u
  cover : ∀ u v, R u v → ∃ i t, SameEdge
    ((cycles i).cycle t,(cycles i).cycle (successor hN t)) (u,v)
  unique : ∀ i t j s, SameEdge
    ((cycles i).cycle t,(cycles i).cycle (successor hN t))
    ((cycles j).cycle s,(cycles j).cycle (successor hN s)) → i=j ∧ t=s

theorem cycle_injective {V R N hN} (C : CycleData V R N hN) :
    Function.Injective C.cycle := by
  intro s t h
  simpa only [C.position_cycle] using congrArg C.position h

theorem cycle_surjective {V R N hN} (C : CycleData V R N hN) :
    Function.Surjective C.cycle := by
  intro v
  exact ⟨C.position v,C.cycle_position v⟩

/-- A short finite list cannot contain every actual cyclic position. -/
theorem fin_escape_short_list {N : Nat} (l : List (Fin N)) (hl : l.length<N) :
    ∃ t : Fin N, t ∉ l := by
  classical
  apply Classical.byContradiction
  intro hn
  have hall : ∀ t : Fin N, t ∈ l := by
    intro t
    apply Classical.byContradiction
    intro ht
    exact hn ⟨t,ht⟩
  have hsub : List.finRange N ⊆ l := by
    intro t _
    exact hall t
  have hle := (List.nodup_finRange N).length_le_of_subset hsub
  simp only [List.length_finRange] at hle
  omega

private theorem pair_flatMap_length {A B : Type} (l : List A) (f g : A → B) :
    (l.flatMap fun a => [f a,g a]).length = 2*l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons,List.length_append,
      List.length_cons,List.length_nil] at *; omega

/-- Each blocked vertex excludes its own position and the preceding edge
position. Repeated blocked vertices cause no difficulty. -/
def blockedPositions {V R N hN} (C : CycleData V R N hN) (blocked : List V) :
    List (Fin N) := blocked.flatMap fun v =>
      [C.position v,predecessor hN (C.position v)]

theorem blockedPositions_length {V R N hN} (C : CycleData V R N hN)
    (blocked : List V) : (blockedPositions C blocked).length=2*blocked.length :=
  pair_flatMap_length blocked C.position (fun v => predecessor hN (C.position v))

theorem blocked_start {V R N hN} (C : CycleData V R N hN) (blocked : List V)
    (t : Fin N) (h : C.cycle t ∈ blocked) : t ∈ blockedPositions C blocked := by
  apply List.mem_flatMap.mpr
  refine ⟨C.cycle t,h,?_⟩
  simp [C.position_cycle]

theorem blocked_finish {V R N hN} (C : CycleData V R N hN) (blocked : List V)
    (t : Fin N) (h : C.cycle (successor hN t) ∈ blocked) :
    t ∈ blockedPositions C blocked := by
  apply List.mem_flatMap.mpr
  refine ⟨C.cycle (successor hN t),h,?_⟩
  simp [C.position_cycle,predecessor_successor]

/-- A real edge of the Hamilton tour avoids every blocked vertex whenever
twice the blocked list length is smaller than the cycle. -/
theorem edge_avoiding_vertices {V R N hN} (C : CycleData V R N hN)
    (blocked : List V) (hroom : 2*blocked.length<N) :
    ∃ t : Fin N, C.cycle t ∉ blocked ∧ C.cycle (successor hN t) ∉ blocked := by
  have hshort : (blockedPositions C blocked).length<N := by
    rw [blockedPositions_length]
    exact hroom
  obtain ⟨t,ht⟩ := fin_escape_short_list (blockedPositions C blocked) hshort
  exact ⟨t,fun h => ht (blocked_start C blocked t h),
    fun h => ht (blocked_finish C blocked t h)⟩

/-- All endpoints of one selected actual edge from each factor, in factor order. -/
def endpointList {V R m N hN} (cycles : Fin m → CycleData V R N hN)
    (selected : Fin m → Fin N) : List V :=
  (List.finRange m).flatMap fun i =>
    [(cycles i).cycle (selected i),(cycles i).cycle (successor hN (selected i))]

theorem endpointList_length {V R m N hN} (cycles : Fin m → CycleData V R N hN)
    (selected : Fin m → Fin N) : (endpointList cycles selected).length=2*m := by
  unfold endpointList
  rw [pair_flatMap_length,List.length_finRange]

def extendSelection {k N : Nat} (f : Fin k → Fin N) (t : Fin N) :
    Fin (k+1) → Fin N := fun i =>
  if h : i.val<k then f ⟨i.val,h⟩ else t

theorem extendSelection_old {k N : Nat} (f : Fin k → Fin N) (t : Fin N)
    (i : Fin k) : extendSelection f t i.castSucc=f i := by
  simp only [extendSelection,Fin.val_castSucc,dite_eq_left i.isLt]

theorem extendSelection_last {k N : Nat} (f : Fin k → Fin N) (t : Fin N) :
    extendSelection f t (Fin.last k)=t := by
  simp [extendSelection]

theorem endpointList_extend {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN) (f : Fin k → Fin N) (t : Fin N) :
    endpointList cycles (extendSelection f t) =
      endpointList (fun i => cycles i.castSucc) f ++
        [(cycles (Fin.last k)).cycle t,
         (cycles (Fin.last k)).cycle (successor hN t)] := by
  unfold endpointList
  rw [List.finRange_succ_last,List.flatMap_append,List.flatMap_map]
  simp only [extendSelection_old,List.flatMap_cons,List.flatMap_nil,
    extendSelection_last,List.append_nil]

/-- Uniform greedy orthogonal matching. The conclusion says every endpoint
of every selected factor edge is distinct; no rainbow-matching assumption. -/
theorem select_disjoint_edges {V : Type} {R : V → V → Prop} {N : Nat}
    (hN : 0<N) (hloop : ∀ v, ¬ R v v) (m : Nat)
    (cycles : Fin m → CycleData V R N hN) (hroom : 4*(m-1)<N) :
    ∃ selected : Fin m → Fin N, (endpointList cycles selected).Nodup := by
  induction m with
  | zero =>
    refine ⟨fun i => Fin.elim0 i,?_⟩
    simp [endpointList]
  | succ k ih =>
    have htail : 4*(k-1)<N := by omega
    obtain ⟨f,hf⟩ := ih (fun i => cycles i.castSucc) htail
    let blocked := endpointList (fun i => cycles i.castSucc) f
    have hlen : blocked.length=2*k := endpointList_length _ _
    have hfree : 2*blocked.length<N := by omega
    obtain ⟨t,hstart,hfinish⟩ :=
      edge_avoiding_vertices (cycles (Fin.last k)) blocked hfree
    have hne : (cycles (Fin.last k)).cycle t ≠
        (cycles (Fin.last k)).cycle (successor hN t) := by
      intro he
      have ha := (cycles (Fin.last k)).adjacent t
      rw [he] at ha
      exact hloop _ ha
    refine ⟨extendSelection f t,?_⟩
    rw [endpointList_extend,List.nodup_append]
    refine ⟨hf,?_,?_⟩
    · simpa using hne
    · intro a ha b hb hab
      simp at hb
      rcases hb with rfl | rfl
      · exact hstart (hab ▸ ha)
      · exact hfinish (hab ▸ ha)

theorem decomposition_select_disjoint_edges {V R m N hN}
    (D : DecompositionData V R m N hN) (hroom : 4*(m-1)<N) :
    ∃ selected : Fin m → Fin N, (endpointList D.cycles selected).Nodup :=
  select_disjoint_edges hN D.loopfree m D.cycles hroom

/-- The greedy room bound holds uniformly in every even cube dimension. -/
theorem even_cube_room (m : Nat) : 4*(m-1)<2^(2*m) := by
  have hsmall : ∀ k : Nat, k<4^k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ]
      omega
  rw [Nat.pow_mul]
  change 4*(m-1)<4^m
  cases m with
  | zero => simp
  | succ k =>
    have hk := hsmall k
    simp only [Nat.add_sub_cancel,Nat.pow_succ]
    omega

/-- In a genuine decomposition of an even cube, an orthogonal choice of
one edge per Hamilton factor requires no additional matching hypothesis. -/
theorem even_cube_select_disjoint_edges {V R m hN}
    (D : DecompositionData V R m (2^(2*m)) hN) :
    ∃ selected : Fin m → Fin (2^(2*m)), (endpointList D.cycles selected).Nodup :=
  decomposition_select_disjoint_edges D (even_cube_room m)

#print axioms select_disjoint_edges
#print axioms decomposition_select_disjoint_edges
#print axioms even_cube_select_disjoint_edges
end ErdePaths.HamiltonData
