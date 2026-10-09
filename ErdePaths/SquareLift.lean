import ErdePaths.Basic

namespace ErdePaths.SquareLift

/-- Source index of a nonterminal macro vertex. -/
def sourceIndex {ℓ N : Nat} (_hN : 0 < N) (t : Fin (ℓ * N)) : Fin (ℓ + 1) :=
  ⟨t.val / N, by
    have hlt : t.val / N < ℓ := Nat.div_lt_of_lt_mul
      (by simpa only [Nat.mul_comm] using t.isLt)
    omega⟩

/-- Position inside a macro of N edges. -/
def macroIndex {ℓ N : Nat} (hN : 0 < N) (t : Fin (ℓ * N)) : Fin N :=
  ⟨t.val % N, Nat.mod_lt _ hN⟩

/-- The nonterminal vertices occupy full source fibers. The j-th permutation
specifies the order in which the macro visits its source fiber. -/
def nonterminal {V : Type} {ℓ N : Nat} (hN : 0 < N)
    (base : Fin (ℓ + 1) → V) (fiber : Fin (ℓ + 1) → Fin N → V)
    (t : Fin (ℓ * N)) : V × V :=
  (base (sourceIndex hN t), fiber (sourceIndex hN t) (macroIndex hN t))

/-- Macro expansion including the final diagonal endpoint. -/
def expand {V : Type} {ℓ N : Nat} (hN : 0 < N)
    (base : Fin (ℓ + 1) → V) (fiber : Fin (ℓ + 1) → Fin N → V)
    (t : Fin (ℓ * N + 1)) : V × V :=
  if ht : t.val < ℓ * N then nonterminal hN base fiber ⟨t.val, ht⟩
  else (base ⟨ℓ, by omega⟩, base ⟨ℓ, by omega⟩)

/-- Unique source and unique position in a source fiber force unique expanded position. -/
theorem nonterminal_injective {V : Type} {ℓ N : Nat} (hN : 0 < N)
    {base : Fin (ℓ + 1) → V} (hbase : Function.Injective base)
    {fiber : Fin (ℓ + 1) → Fin N → V}
    (hfiber : ∀ j, Function.Injective (fiber j)) :
    Function.Injective (nonterminal hN base fiber) := by
  intro s t h
  have hs : sourceIndex hN s = sourceIndex hN t := hbase (congrArg Prod.fst h)
  have hf : macroIndex hN s = macroIndex hN t := by
    apply hfiber (sourceIndex hN t)
    have hh := congrArg Prod.snd h
    simpa [nonterminal, hs] using hh
  have hq : s.val / N = t.val / N := congrArg Fin.val hs
  have hr : s.val % N = t.val % N := congrArg Fin.val hf
  apply Fin.ext
  have heq := Nat.div_add_mod s.val N
  have heq' := Nat.div_add_mod t.val N
  rw [hq, hr] at heq
  omega

/-- Central simplicity lemma for the audited diagonal macro lift.
No graph or adjacency assumptions are needed for vertex non-repetition. -/
theorem expand_injective {V : Type} {ℓ N : Nat} (hN : 0 < N)
    {base : Fin (ℓ + 1) → V} (hbase : Function.Injective base)
    {fiber : Fin (ℓ + 1) → Fin N → V}
    (hfiber : ∀ j, Function.Injective (fiber j)) :
    Function.Injective (expand hN base fiber) := by
  intro s t h
  by_cases hs : s.val < ℓ * N <;> by_cases ht : t.val < ℓ * N
  · have he : (⟨s.val, hs⟩ : Fin (ℓ * N)) = ⟨t.val, ht⟩ :=
      nonterminal_injective hN hbase hfiber (by simpa [expand, hs, ht] using h)
    exact Fin.ext (congrArg (fun z : Fin (ℓ * N) => z.val) he)
  · have he : base (sourceIndex hN ⟨s.val, hs⟩) = base ⟨ℓ, by omega⟩ :=
      congrArg Prod.fst (by simpa [expand, hs, ht] using h)
    have he' := congrArg Fin.val (hbase he)
    have hlt : s.val / N < ℓ := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hs)
    simp only [sourceIndex] at he'
    omega
  · have he : base ⟨ℓ, by omega⟩ = base (sourceIndex hN ⟨t.val, ht⟩) :=
      congrArg Prod.fst (by simpa [expand, hs, ht] using h)
    have he' := congrArg Fin.val (hbase he)
    have hlt : t.val / N < ℓ := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using ht)
    simp only [sourceIndex] at he'
    omega
  · apply Fin.ext
    omega

#print axioms expand_injective
private theorem bounded_mod {N x : Nat} (hx : x < 2 * N) :
    x % N = if x < N then x else x - N := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Clockwise rotation of a finite cycle index. -/
def forward {N : Nat} (hN : 0 < N) (i r : Fin N) : Fin N :=
  ⟨(i.val + r.val) % N, Nat.mod_lt _ hN⟩

/-- Counterclockwise rotation of a finite cycle index. -/
def backward {N : Nat} (hN : 0 < N) (i r : Fin N) : Fin N :=
  ⟨(N - r.val + i.val) % N, Nat.mod_lt _ hN⟩

theorem forward_injective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Injective (forward hN i) := by
  intro r s h
  have he := congrArg Fin.val h
  dsimp [forward] at he
  rw [bounded_mod (by have := i.isLt; have := r.isLt; omega),
      bounded_mod (by have := i.isLt; have := s.isLt; omega)] at he
  apply Fin.ext
  split at he <;> split at he <;> have := r.isLt <;> have := s.isLt <;> omega

theorem backward_injective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Injective (backward hN i) := by
  intro r s h
  have he := congrArg Fin.val h
  dsimp [backward] at he
  rw [bounded_mod (by have := i.isLt; omega),
      bounded_mod (by have := i.isLt; omega)] at he
  apply Fin.ext
  split at he <;> split at he <;> have := r.isLt <;> have := s.isLt <;> omega

/-- Explicit inverse witness for a clockwise rotation. -/
theorem forward_inverse {N : Nat} (hN : 0 < N) (i v : Fin N) :
    forward hN i (backward hN v i) = v := by
  apply Fin.ext
  dsimp [forward, backward]
  have hm : (N - i.val + v.val) % N =
      if N - i.val + v.val < N then N - i.val + v.val else N - i.val + v.val - N :=
    bounded_mod (by have := v.isLt; omega)
  rw [hm]
  split
  · rw [Nat.mod_eq_sub_mod (by have := i.isLt; omega), Nat.mod_eq_of_lt (by have := v.isLt; omega)]
    have := i.isLt
    omega
  · rw [Nat.mod_eq_of_lt (by have := v.isLt; omega)]
    have := i.isLt
    omega

theorem forward_surjective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Surjective (forward hN i) := by
  intro v
  exact ⟨backward hN v i, forward_inverse hN i v⟩

/-- Explicit inverse witness for a counterclockwise rotation. -/
theorem backward_inverse {N : Nat} (hN : 0 < N) (i v : Fin N) :
    backward hN i (backward hN i v) = v := by
  apply Fin.ext
  dsimp [backward]
  have hm : (N - v.val + i.val) % N =
      if N - v.val + i.val < N then N - v.val + i.val else N - v.val + i.val - N :=
    bounded_mod (by have := i.isLt; omega)
  rw [hm]
  split
  · rw [Nat.mod_eq_of_lt (by have := i.isLt; have := v.isLt; omega)]
    have := i.isLt
    have := v.isLt
    omega
  · rw [Nat.mod_eq_sub_mod (by have := i.isLt; have := v.isLt; omega),
      Nat.mod_eq_of_lt (by have := i.isLt; have := v.isLt; omega)]
    have := i.isLt
    have := v.isLt
    omega

theorem backward_surjective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Surjective (backward hN i) := by
  intro v
  exact ⟨backward hN i v, backward_inverse hN i v⟩

/-- Successor and predecessor along the cycle. -/
def successor {N : Nat} (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(i.val + 1) % N, Nat.mod_lt _ hN⟩
def predecessor {N : Nat} (hN : 0 < N) (i : Fin N) : Fin N :=
  ⟨(N - 1 + i.val) % N, Nat.mod_lt _ hN⟩

theorem backward_zero {N : Nat} (hN : 0 < N) (i : Fin N) :
    backward hN i ⟨0,hN⟩ = i := by
  apply Fin.ext
  simp [backward, Nat.mod_eq_of_lt i.isLt]

theorem forward_zero {N : Nat} (hN : 0 < N) (i : Fin N) :
    forward hN i ⟨0,hN⟩ = i := by
  apply Fin.ext
  simp [forward, Nat.mod_eq_of_lt i.isLt]

theorem backward_last {N : Nat} (hN : 0 < N) (i : Fin N) :
    backward hN i ⟨N-1,by omega⟩ = successor hN i := by
  apply Fin.ext
  dsimp [backward, successor]
  congr 1
  omega

theorem forward_last {N : Nat} (hN : 0 < N) (i : Fin N) :
    forward hN i ⟨N-1,by omega⟩ = predecessor hN i := by
  apply Fin.ext
  simp [forward, predecessor, Nat.add_comm]

/-- Each nonconnector plus edge traverses the underlying cycle backwards. -/
theorem successor_backward_step {N r : Nat} (hN : 0 < N) (i : Fin N)
    (hr : r+1 < N) :
    successor hN (backward hN i ⟨r+1,hr⟩) = backward hN i ⟨r,by omega⟩ := by
  apply Fin.ext
  dsimp [successor, backward]
  rw [Nat.mod_add_mod]
  congr 1
  omega

/-- Each nonconnector minus edge traverses the underlying cycle forwards. -/
theorem successor_forward_step {N r : Nat} (hN : 0 < N) (i : Fin N)
    (hr : r+1 < N) :
    successor hN (forward hN i ⟨r,by omega⟩) = forward hN i ⟨r+1,hr⟩ := by
  apply Fin.ext
  dsimp [successor, forward]
  rw [Nat.mod_add_mod]
  congr 1

/-- Explicit cyclic fibers fulfill the generic simplicity hypotheses. -/
theorem expand_cyclic_injective {V : Type} {ℓ N : Nat} (hN : 0 < N)
    {base : Fin (ℓ+1) → V} (hbase : Function.Injective base)
    (cycles : Fin (ℓ+1) → Fin N → V)
    (hcycles : ∀ j, Function.Injective (cycles j)) (phase : Fin (ℓ+1) → Fin N) :
    Function.Injective (expand hN base
      (fun j r => cycles j (backward hN (phase j) r))) := by
  apply expand_injective hN hbase
  intro j r s h
  exact backward_injective hN (phase j) (hcycles j h)

/-- Clockwise cycles can be used for the transposed/reversed lift. -/
theorem expand_cyclic_forward_injective {V : Type} {ℓ N : Nat} (hN : 0 < N)
    {base : Fin (ℓ+1) → V} (hbase : Function.Injective base)
    (cycles : Fin (ℓ+1) → Fin N → V)
    (hcycles : ∀ j, Function.Injective (cycles j)) (phase : Fin (ℓ+1) → Fin N) :
    Function.Injective (expand hN base
      (fun j r => cycles j (forward hN (phase j) r))) := by
  apply expand_injective hN hbase
  intro j r s h
  exact forward_injective hN (phase j) (hcycles j h)

/-- An explicit plus macro has N-1 vertical steps followed by a horizontal connector. -/
def plusMacro {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) (r : Fin (N+1)) : V × V :=
  if hr : r.val < N then (cycle i, cycle (backward hN i ⟨r.val,hr⟩))
  else (cycle (successor hN i), cycle (successor hN i))

theorem plusMacro_start {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    plusMacro hN cycle i ⟨0,by omega⟩ = (cycle i,cycle i) := by
  simp [plusMacro, hN, backward_zero]

theorem plusMacro_before_connector {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    plusMacro hN cycle i ⟨N-1,by omega⟩ = (cycle i,cycle (successor hN i)) := by
  have hr : N-1 < N := by omega
  simp [plusMacro, hr, backward_last]

theorem plusMacro_end {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    plusMacro hN cycle i ⟨N,by omega⟩ =
      (cycle (successor hN i), cycle (successor hN i)) := by
  simp [plusMacro]

/-- Each plus long vertical arc is labeled by its clockwise source index. -/
def plusLongIndex {N : Nat} (hN : 0 < N) (i : Fin N) (r : Fin (N-1)) : Fin N :=
  backward hN i ⟨r.val+1,by have := r.isLt; omega⟩

/-- The plus macro uses every vertical cycle arc except the omitted i→i+1 arc. -/
theorem plusLongIndex_image {N : Nat} (hN : 0 < N) (i j : Fin N) :
    (∃ r : Fin (N-1), plusLongIndex hN i r = j) ↔ j ≠ i := by
  constructor
  · rintro ⟨r,he⟩ hji
    have hh : backward hN i ⟨r.val+1,by have := r.isLt; omega⟩ = backward hN i ⟨0,hN⟩ := by
      simpa [plusLongIndex, backward_zero, hji] using he
    have hh' := congrArg (fun z : Fin N => z.val) (backward_injective hN i hh)
    dsimp at hh'
    omega
  · intro hji
    obtain ⟨r,hr⟩ := backward_surjective hN i j
    have hr0 : r.val ≠ 0 := by
      intro he
      have he' : r = ⟨0,hN⟩ := Fin.ext he
      apply hji
      simpa [he', backward_zero] using hr.symm
    refine ⟨⟨r.val-1,by have := r.isLt; omega⟩, ?_⟩
    have he' : (⟨r.val-1+1,by have := r.isLt; omega⟩ : Fin N) = r := Fin.ext (by change r.val-1+1 = r.val; omega)
    simpa [plusLongIndex, he'] using hr

theorem plusLongIndex_injective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Injective (plusLongIndex hN i) := by
  intro r s h
  have he := congrArg Fin.val (backward_injective hN i h)
  exact Fin.ext (by dsimp at he; omega)

/-- Exact coordinate formula for every long edge of the plus macro. -/
theorem plusMacro_long_step {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) (r : Fin (N-1)) :
    (plusMacro hN cycle i ⟨r.val,by have := r.isLt; omega⟩,
      plusMacro hN cycle i ⟨r.val+1,by have := r.isLt; omega⟩) =
    ((cycle i, cycle (successor hN (plusLongIndex hN i r))),
      (cycle i, cycle (plusLongIndex hN i r))) := by
  have hr : r.val+1 < N := by have := r.isLt; omega
  simp [plusMacro, plusLongIndex, hr, (by omega : r.val < N), successor_backward_step]

/-- Minus macros interchange the coordinate roles and traverse forward before their connector. -/
def minusMacro {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) (r : Fin (N+1)) : V × V :=
  if hr : r.val < N then (cycle (forward hN i ⟨r.val,hr⟩), cycle i)
  else (cycle (predecessor hN i), cycle (predecessor hN i))

theorem minusMacro_start {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    minusMacro hN cycle i ⟨0,by omega⟩ = (cycle i,cycle i) := by
  simp [minusMacro, hN, forward_zero]

theorem minusMacro_before_connector {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    minusMacro hN cycle i ⟨N-1,by omega⟩ = (cycle (predecessor hN i),cycle i) := by
  have hr : N-1 < N := by omega
  simp [minusMacro, hr, forward_last]

theorem minusMacro_end {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    minusMacro hN cycle i ⟨N,by omega⟩ =
      (cycle (predecessor hN i), cycle (predecessor hN i)) := by
  simp [minusMacro]

/-- Labels of the long horizontal arcs used by a minus macro. -/
def minusLongIndex {N : Nat} (hN : 0 < N) (i : Fin N) (r : Fin (N-1)) : Fin N :=
  forward hN i ⟨r.val,by have := r.isLt; omega⟩

/-- The minus macro omits exactly the predecessor→i horizontal arc. -/
theorem minusLongIndex_image {N : Nat} (hN : 0 < N) (i j : Fin N) :
    (∃ r : Fin (N-1), minusLongIndex hN i r = j) ↔ j ≠ predecessor hN i := by
  constructor
  · rintro ⟨r,he⟩ hji
    have hh : forward hN i ⟨r.val,by have := r.isLt; omega⟩ = forward hN i ⟨N-1,by omega⟩ := by
      simpa [minusLongIndex, forward_last, hji] using he
    have hh' := congrArg Fin.val (forward_injective hN i hh)
    have := r.isLt
    dsimp at hh'
    omega
  · intro hji
    obtain ⟨r,hr⟩ := forward_surjective hN i j
    have hrlt : r.val < N-1 := by
      have hneq : r.val ≠ N-1 := by
        intro he
        have he' : r = ⟨N-1,by omega⟩ := Fin.ext he
        apply hji
        simpa [he', forward_last] using hr.symm
      have := r.isLt
      omega
    refine ⟨⟨r.val,hrlt⟩, ?_⟩
    exact hr

theorem minusLongIndex_injective {N : Nat} (hN : 0 < N) (i : Fin N) :
    Function.Injective (minusLongIndex hN i) := by
  intro r s h
  exact Fin.ext (congrArg (fun z : Fin N => z.val) (forward_injective hN i h))

/-- Exact coordinate formula for every long edge of the minus macro. -/
theorem minusMacro_long_step {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) (r : Fin (N-1)) :
    (minusMacro hN cycle i ⟨r.val,by have := r.isLt; omega⟩,
      minusMacro hN cycle i ⟨r.val+1,by have := r.isLt; omega⟩) =
    ((cycle (minusLongIndex hN i r), cycle i),
      (cycle (successor hN (minusLongIndex hN i r)), cycle i)) := by
  have hr : r.val+1 < N := by have := r.isLt; omega
  simp [minusMacro, minusLongIndex, hr, (by omega : r.val < N), successor_forward_step]

 theorem successor_predecessor {N : Nat} (hN : 0 < N) (i : Fin N) :
    successor hN (predecessor hN i) = i := by
  apply Fin.ext
  dsimp [successor, predecessor]
  rw [Nat.mod_add_mod]
  have he : N-1+i.val+1 = N+i.val := by omega
  rw [he]
  simp [Nat.mod_eq_of_lt i.isLt]

 theorem predecessor_successor {N : Nat} (hN : 0 < N) (i : Fin N) :
    predecessor hN (successor hN i) = i := by
  apply Fin.ext
  dsimp [successor, predecessor]
  rw [Nat.add_mod_mod]
  have he : N-1+(i.val+1) = N+i.val := by omega
  rw [he]
  simp [Nat.mod_eq_of_lt i.isLt]

/-- Edge labels of C_N□C_N: horizontal labels are (row, arc source),
vertical labels are (column, arc source). For N≥3 these describe undirected
cycle-product edges without ambiguity. -/
abbrev TorusEdgeLabel (N : Nat) := (Fin N × Fin N) ⊕ (Fin N × Fin N)

/-- Exact label assigned to each of the N edges of a plus macro. -/
def plusLabel {N : Nat} (hN : 0 < N) (i r : Fin N) : TorusEdgeLabel N :=
  if hr : r.val+1 < N then
    .inr (i, backward hN i ⟨r.val+1,hr⟩)
  else .inl (successor hN i,i)

/-- Exact label assigned to each of the N edges of a minus macro. -/
def minusLabel {N : Nat} (hN : 0 < N) (i r : Fin N) : TorusEdgeLabel N :=
  if r.val+1 < N then .inl (i,forward hN i r)
  else .inr (predecessor hN i,predecessor hN i)

/-- A vertical labeled edge occurs in plus precisely when it is not the omitted diagonal arc. -/
theorem plus_vertical_image {N : Nat} (hN : 0 < N) (col arc : Fin N) :
    (∃ i r, plusLabel hN i r = .inr (col,arc)) ↔ arc ≠ col := by
  constructor
  · rintro ⟨i,r,he⟩
    unfold plusLabel at he
    split at he
    · have hh : i = col ∧ backward hN i ⟨r.val+1,by assumption⟩ = arc := by
        simpa only [Sum.inr.injEq, Prod.mk.injEq] using he
      obtain ⟨r',hr'⟩ : ∃ r' : Fin (N-1), plusLongIndex hN col r' = arc := by
        refine ⟨⟨r.val,by omega⟩, ?_⟩
        simpa [plusLongIndex, hh.1] using hh.2
      exact (plusLongIndex_image hN col arc).mp ⟨r',hr'⟩
    · contradiction
  · intro hneq
    obtain ⟨r,hr⟩ := (plusLongIndex_image hN col arc).mpr hneq
    refine ⟨col,⟨r.val,by have := r.isLt; omega⟩, ?_⟩
    have hrlt : r.val+1 < N := by have := r.isLt; omega
    simpa [plusLabel,hrlt,plusLongIndex] using congrArg (fun a => (Sum.inr (col,a) : TorusEdgeLabel N)) hr

/-- Plus horizontal edges are exactly the connectors at the clockwise target row. -/
theorem plus_horizontal_image {N : Nat} (hN : 0 < N) (row arc : Fin N) :
    (∃ i r, plusLabel hN i r = .inl (row,arc)) ↔ row = successor hN arc := by
  constructor
  · rintro ⟨i,r,he⟩
    unfold plusLabel at he
    split at he
    · contradiction
    · have hh : successor hN i = row ∧ i = arc := by
        simpa only [Sum.inl.injEq, Prod.mk.injEq] using he
      simpa [hh.2] using hh.1.symm
  · intro he
    refine ⟨arc,⟨N-1,by omega⟩, ?_⟩
    have hh : ¬(N-1+1 < N) := by omega
    simp [plusLabel,hh,he]

/-- Minus horizontal arcs are exactly those not omitted before the source row. -/
theorem minus_horizontal_image {N : Nat} (hN : 0 < N) (row arc : Fin N) :
    (∃ i r, minusLabel hN i r = .inl (row,arc)) ↔ arc ≠ predecessor hN row := by
  constructor
  · rintro ⟨i,r,he⟩
    unfold minusLabel at he
    split at he
    · have hh : i = row ∧ forward hN i r = arc := by
        simpa only [Sum.inl.injEq, Prod.mk.injEq] using he
      obtain ⟨r',hr'⟩ : ∃ r' : Fin (N-1), minusLongIndex hN row r' = arc := by
        refine ⟨⟨r.val,by omega⟩, ?_⟩
        simpa [minusLongIndex, hh.1] using hh.2
      exact (minusLongIndex_image hN row arc).mp ⟨r',hr'⟩
    · contradiction
  · intro hneq
    obtain ⟨r,hr⟩ := (minusLongIndex_image hN row arc).mpr hneq
    refine ⟨row,⟨r.val,by have := r.isLt; omega⟩, ?_⟩
    have hrlt : r.val+1 < N := by have := r.isLt; omega
    simpa [minusLabel,hrlt,minusLongIndex] using congrArg (fun a => (Sum.inl (row,a) : TorusEdgeLabel N)) hr

/-- Minus vertical edges are exactly the omitted diagonal arcs, used as connectors. -/
theorem minus_vertical_image {N : Nat} (hN : 0 < N) (col arc : Fin N) :
    (∃ i r, minusLabel hN i r = .inr (col,arc)) ↔ col = arc := by
  constructor
  · rintro ⟨i,r,he⟩
    unfold minusLabel at he
    split at he
    · contradiction
    · have hh : predecessor hN i = col ∧ predecessor hN i = arc := by
        simpa only [Sum.inr.injEq, Prod.mk.injEq] using he
      exact hh.1.symm.trans hh.2
  · rintro rfl
    refine ⟨successor hN col,⟨N-1,by omega⟩, ?_⟩
    have hh : ¬(N-1+1 < N) := by omega
    simp [minusLabel,hh,predecessor_successor]

/-- Every torus edge label lies in exactly one of the explicit macro families.
Unique occurrence *within* the selected family is proved separately below. -/
theorem torus_label_partition {N : Nat} (hN : 0 < N) (e : TorusEdgeLabel N) :
    ((∃ i r, plusLabel hN i r = e) ∧ ¬∃ i r, minusLabel hN i r = e) ∨
    ((∃ i r, minusLabel hN i r = e) ∧ ¬∃ i r, plusLabel hN i r = e) := by
  cases e with
  | inl e =>
    rw [plus_horizontal_image,minus_horizontal_image]
    have he : e.1 = successor hN e.2 ↔ e.2 = predecessor hN e.1 := by
      constructor
      · intro h
        simp [h,predecessor_successor]
      · intro h
        simp [h,successor_predecessor]
    rw [he]
    by_cases h : e.2 = predecessor hN e.1
    · exact Or.inl ⟨h,by simpa using h⟩
    · exact Or.inr ⟨h,h⟩
  | inr e =>
    rw [plus_vertical_image,minus_vertical_image]
    by_cases h : e.1 = e.2
    · exact Or.inr ⟨h,by intro hne; exact hne h.symm⟩
    · exact Or.inl ⟨Ne.symm h,h⟩

/-- No two plus macro positions own the same torus edge label. -/
theorem plusLabel_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (fun a : Fin N × Fin N => plusLabel hN a.1 a.2) := by
  intro a b he
  by_cases ha : a.2.val+1 < N <;> by_cases hb : b.2.val+1 < N
  · simp [plusLabel,ha,hb] at he
    obtain ⟨h1,h2⟩ := he
    have h2' := backward_injective hN b.1 (by simpa [h1] using h2)
    apply Prod.ext h1
    apply Fin.ext
    have hh := congrArg (fun z : Fin N => z.val) h2'
    dsimp at hh
    omega
  · simp [plusLabel,ha,hb] at he
  · simp [plusLabel,ha,hb] at he
  · simp [plusLabel,ha,hb] at he
    apply Prod.ext he.2
    apply Fin.ext
    have := a.2.isLt
    have := b.2.isLt
    omega

/-- No two minus macro positions own the same torus edge label. -/
theorem minusLabel_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (fun a : Fin N × Fin N => minusLabel hN a.1 a.2) := by
  intro a b he
  by_cases ha : a.2.val+1 < N <;> by_cases hb : b.2.val+1 < N
  · simp [minusLabel,ha,hb] at he
    obtain ⟨h1,h2⟩ := he
    exact Prod.ext h1 (forward_injective hN b.1 (by simpa [h1] using h2))
  · simp [minusLabel,ha,hb] at he
  · simp [minusLabel,ha,hb] at he
  · simp [minusLabel,ha,hb] at he
    have h1 := congrArg (successor hN) he
    simp only [successor_predecessor] at h1
    apply Prod.ext h1
    apply Fin.ext
    have := a.2.isLt
    have := b.2.isLt
    omega

/-- Decoding a label gives the corresponding product edge in its clockwise orientation. -/
def decode {V : Type} {N : Nat} (hN : 0 < N) (cycle : Fin N → V)
    (e : TorusEdgeLabel N) : (V × V) × (V × V) :=
  match e with
  | .inl (row,arc) => ((cycle arc,cycle row),(cycle (successor hN arc),cycle row))
  | .inr (col,arc) => ((cycle col,cycle arc),(cycle col,cycle (successor hN arc)))

/-- Orientations are forgotten only when comparing actual undirected edges. -/
def SameEdge {α : Type} (e f : α × α) : Prop := e = f ∨ e = (f.2,f.1)

/-- The actual plus macro step realizes exactly its assigned edge label. -/
theorem plus_step_decodes {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i r : Fin N) :
    SameEdge (plusMacro hN cycle i r.castSucc, plusMacro hN cycle i r.succ)
      (decode hN cycle (plusLabel hN i r)) := by
  by_cases hr : r.val+1 < N
  · right
    have hh := plusMacro_long_step hN cycle i (⟨r.val,by omega⟩ : Fin (N-1))
    simpa [decode,plusLabel,hr,plusLongIndex,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using hh
  · left
    have he : r.val = N-1 := by have := r.isLt; omega
    have he1 : r.castSucc = (⟨N-1,by omega⟩ : Fin (N+1)) := Fin.ext he
    have he2 : r.succ = (⟨N,by omega⟩ : Fin (N+1)) := Fin.ext (by dsimp; omega)
    rw [he1,he2,plusMacro_before_connector,plusMacro_end]
    simp [decode,plusLabel,hr]

/-- The actual minus macro step realizes exactly its assigned edge label. -/
theorem minus_step_decodes {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i r : Fin N) :
    SameEdge (minusMacro hN cycle i r.castSucc, minusMacro hN cycle i r.succ)
      (decode hN cycle (minusLabel hN i r)) := by
  by_cases hr : r.val+1 < N
  · left
    have hh := minusMacro_long_step hN cycle i (⟨r.val,by omega⟩ : Fin (N-1))
    simpa [decode,minusLabel,hr,minusLongIndex,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using hh
  · right
    have he : r.val = N-1 := by have := r.isLt; omega
    have he1 : r.castSucc = (⟨N-1,by omega⟩ : Fin (N+1)) := Fin.ext he
    have he2 : r.succ = (⟨N,by omega⟩ : Fin (N+1)) := Fin.ext (by dsimp; omega)
    rw [he1,he2,minusMacro_before_connector,minusMacro_end]
    simp [decode,minusLabel,hr,successor_predecessor]

 theorem successor_ne {N : Nat} (hN : 0 < N) (h2 : 2 ≤ N) (i : Fin N) :
    successor hN i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [successor] at hv
  rw [bounded_mod (by have := i.isLt; omega)] at hv
  split at hv <;> omega

 theorem successor_twice_ne {N : Nat} (hN : 0 < N) (h3 : 3 ≤ N) (i : Fin N) :
    successor hN (successor hN i) ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  dsimp [successor] at hv
  rw [Nat.mod_add_mod] at hv
  have hm : (i.val+1)+1 = i.val+2 := by omega
  rw [hm,bounded_mod (by have := i.isLt; omega)] at hv
  split at hv <;> omega

/-- For genuine simple cycles (N≥3), the label decoder is injective even after
forgetting edge orientation. This closes the gap between label partition and
partition of actual undirected product edges. -/
theorem decode_edge_injective {V : Type} {N : Nat} (hN : 0 < N) (h3 : 3 ≤ N)
    {cycle : Fin N → V} (hc : Function.Injective cycle) {e f : TorusEdgeLabel N}
    (he : SameEdge (decode hN cycle e) (decode hN cycle f)) : e = f := by
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      simp only [SameEdge,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · exact congrArg Sum.inl (Prod.ext (hc he.1.2) (hc he.1.1))
      · have h1 := hc he.1.1
        have h2 := hc he.2.1
        rw [h1] at h2
        exact False.elim (successor_twice_ne hN h3 f.2 h2)
    | inr f =>
      simp only [SameEdge,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have h1 := hc he.1.1
        have h2 := hc he.2.1
        exact False.elim (successor_ne hN (by omega) e.2 (h2.trans h1.symm))
      · have h1 := hc he.1.1
        have h2 := hc he.2.1
        exact False.elim (successor_ne hN (by omega) e.2 (h2.trans h1.symm))
  | inr e =>
    cases f with
    | inl f =>
      simp only [SameEdge,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · have h1 := hc he.1.1
        have h2 := hc he.2.1
        exact False.elim (successor_ne hN (by omega) f.2 (h2.symm.trans h1))
      · have h1 := hc he.1.1
        have h2 := hc he.2.1
        exact False.elim (successor_ne hN (by omega) f.2 (h1.symm.trans h2))
    | inr f =>
      simp only [SameEdge,decode,Prod.mk.injEq] at he
      rcases he with he | he
      · exact congrArg Sum.inr (Prod.ext (hc he.1.1) (hc he.1.2))
      · have h1 := hc he.1.2
        have h2 := hc he.2.2
        rw [h1] at h2
        exact False.elim (successor_twice_ne hN h3 f.2 h2)

/-- Macro positions distinguish the plus and minus families. -/
abbrev MacroPosition (N : Nat) := (Fin N × Fin N) ⊕ (Fin N × Fin N)

def macroLabel {N : Nat} (hN : 0 < N) : MacroPosition N → TorusEdgeLabel N
  | .inl (i,r) => plusLabel hN i r
  | .inr (i,r) => minusLabel hN i r

theorem macroLabel_injective {N : Nat} (hN : 0 < N) : Function.Injective (macroLabel hN) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (plusLabel_injective hN he)
    | inr b =>
      have hp : ∃ i r, plusLabel hN i r = plusLabel hN a.1 a.2 := ⟨a.1,a.2,rfl⟩
      have hm : ∃ i r, minusLabel hN i r = plusLabel hN a.1 a.2 := ⟨b.1,b.2,he.symm⟩
      rcases torus_label_partition hN (plusLabel hN a.1 a.2) with h | h
      · exact False.elim (h.2 hm)
      · exact False.elim (h.2 hp)
  | inr a =>
    cases b with
    | inl b =>
      have hp : ∃ i r, plusLabel hN i r = minusLabel hN a.1 a.2 := ⟨b.1,b.2,he.symm⟩
      have hm : ∃ i r, minusLabel hN i r = minusLabel hN a.1 a.2 := ⟨a.1,a.2,rfl⟩
      rcases torus_label_partition hN (minusLabel hN a.1 a.2) with h | h
      · exact False.elim (h.2 hm)
      · exact False.elim (h.2 hp)
    | inr b => exact congrArg Sum.inr (minusLabel_injective hN he)

theorem macroLabel_surjective {N : Nat} (hN : 0 < N) : Function.Surjective (macroLabel hN) := by
  intro e
  rcases torus_label_partition hN e with h | h
  · obtain ⟨i,r,hr⟩ := h.1
    exact ⟨.inl (i,r),hr⟩
  · obtain ⟨i,r,hr⟩ := h.1
    exact ⟨.inr (i,r),hr⟩

theorem sameEdge_symm {α : Type} {e f : α × α} (h : SameEdge e f) : SameEdge f e := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    rw [h]

theorem sameEdge_trans {α : Type} {e f g : α × α}
    (h : SameEdge e f) (h' : SameEdge f g) : SameEdge e g := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl (h.trans h')
  · exact Or.inr (h.trans h')
  · exact Or.inr (h.trans (congrArg (fun z : α × α => (z.2,z.1)) h'))
  · left
    rw [h,h']

/-- The actual directed step at a plus or minus macro position. -/
def macroStep {V : Type} {N : Nat} (hN : 0 < N) (cycle : Fin N → V) :
    MacroPosition N → (V × V) × (V × V)
  | .inl (i,r) => (plusMacro hN cycle i r.castSucc, plusMacro hN cycle i r.succ)
  | .inr (i,r) => (minusMacro hN cycle i r.castSucc, minusMacro hN cycle i r.succ)

theorem macroStep_decodes {V : Type} {N : Nat} (hN : 0 < N) (cycle : Fin N → V)
    (a : MacroPosition N) : SameEdge (macroStep hN cycle a) (decode hN cycle (macroLabel hN a)) := by
  cases a with
  | inl a => exact plus_step_decodes hN cycle a.1 a.2
  | inr a => exact minus_step_decodes hN cycle a.1 a.2

/-- Uniform, exact ownership of every actual undirected torus edge by one
step among the two explicit macro families. No factorization assumption is
used: the macros and their label bijection were constructed above. -/
theorem torus_macro_edge_partition {V : Type} {N : Nat} (hN : 0 < N) (h3 : 3 ≤ N)
    {cycle : Fin N → V} (hc : Function.Injective cycle) (e : TorusEdgeLabel N) :
    ∃ a : MacroPosition N, SameEdge (macroStep hN cycle a) (decode hN cycle e) ∧
      ∀ b, SameEdge (macroStep hN cycle b) (decode hN cycle e) → b = a := by
  obtain ⟨a,ha⟩ := macroLabel_surjective hN e
  refine ⟨a,by simpa [ha] using macroStep_decodes hN cycle a, ?_⟩
  intro b hb
  have he : SameEdge (decode hN cycle (macroLabel hN b)) (decode hN cycle e) :=
    sameEdge_trans (sameEdge_symm (macroStep_decodes hN cycle b)) hb
  have hb' := decode_edge_injective hN h3 hc he
  exact macroLabel_injective hN (hb'.trans ha.symm)

/-- Cartesian-product graph adjacency. -/
def ProductAdjacent {V : Type} (R : V → V → Prop) (u v : V × V) : Prop :=
  (u.1 = v.1 ∧ R u.2 v.2) ∨ (u.2 = v.2 ∧ R u.1 v.1)

theorem productAdjacent_symm {V : Type} {R : V → V → Prop}
    (hsym : ∀ u v, R u v → R v u) {u v : V × V}
    (h : ProductAdjacent R u v) : ProductAdjacent R v u := by
  rcases h with h | h
  · exact Or.inl ⟨h.1.symm,hsym _ _ h.2⟩
  · exact Or.inr ⟨h.1.symm,hsym _ _ h.2⟩

theorem decode_adjacent {V : Type} {N : Nat} (hN : 0 < N)
    {R : V → V → Prop} {cycle : Fin N → V}
    (hcycle : ∀ i, R (cycle i) (cycle (successor hN i))) (e : TorusEdgeLabel N) :
    ProductAdjacent R (decode hN cycle e).1 (decode hN cycle e).2 := by
  cases e with
  | inl e => exact Or.inr ⟨rfl,hcycle e.2⟩
  | inr e => exact Or.inl ⟨rfl,hcycle e.2⟩

/-- Every actual macro step is an edge of the product graph. -/
theorem macroStep_adjacent {V : Type} {N : Nat} (hN : 0 < N)
    {R : V → V → Prop} (hsym : ∀ u v, R u v → R v u) {cycle : Fin N → V}
    (hcycle : ∀ i, R (cycle i) (cycle (successor hN i))) (a : MacroPosition N) :
    ProductAdjacent R (macroStep hN cycle a).1 (macroStep hN cycle a).2 := by
  have hadj := decode_adjacent hN hcycle (macroLabel hN a)
  rcases macroStep_decodes hN cycle a with he | he
  · simpa [he] using hadj
  · simpa [he] using productAdjacent_symm hsym hadj

/-- Nonterminal plus vertices, grouped by column and within-column position. -/
def plusVertex {V : Type} {N : Nat} (hN : 0 < N) (cycle : Fin N → V)
    (a : Fin N × Fin N) : V × V := (cycle a.1,cycle (backward hN a.1 a.2))

def minusVertex {V : Type} {N : Nat} (hN : 0 < N) (cycle : Fin N → V)
    (a : Fin N × Fin N) : V × V := (cycle (forward hN a.1 a.2),cycle a.1)

/-- All N² nonterminal plus vertices are distinct. -/
theorem plusVertex_injective {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hc : Function.Injective cycle) :
    Function.Injective (plusVertex hN cycle) := by
  intro a b he
  have h1 := hc (congrArg Prod.fst he)
  have h2 := hc (congrArg Prod.snd he)
  exact Prod.ext h1 (backward_injective hN b.1 (by simpa [h1] using h2))

/-- Plus macros visit every product vertex, when their cycle is spanning. -/
theorem plusVertex_surjective {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hc : Function.Surjective cycle) :
    Function.Surjective (plusVertex hN cycle) := by
  intro v
  obtain ⟨i,hi⟩ := hc v.1
  obtain ⟨j,hj⟩ := hc v.2
  obtain ⟨r,hr⟩ := backward_surjective hN i j
  exact ⟨(i,r),by simp [plusVertex,hi,hr,hj]⟩

/-- All N² nonterminal minus vertices are distinct. -/
theorem minusVertex_injective {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hc : Function.Injective cycle) :
    Function.Injective (minusVertex hN cycle) := by
  intro a b he
  have h1 := hc (congrArg Prod.snd he)
  have h2 := hc (congrArg Prod.fst he)
  exact Prod.ext h1 (forward_injective hN b.1 (by simpa [h1] using h2))

/-- Minus macros also visit every product vertex. -/
theorem minusVertex_surjective {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hc : Function.Surjective cycle) :
    Function.Surjective (minusVertex hN cycle) := by
  intro v
  obtain ⟨i,hi⟩ := hc v.2
  obtain ⟨j,hj⟩ := hc v.1
  obtain ⟨r,hr⟩ := forward_surjective hN i j
  exact ⟨(i,r),by simp [minusVertex,hi,hr,hj]⟩

/-- An indexed simple expanded path gives a list with precisely ℓN+1 distinct vertices. -/
theorem expanded_list_nodup {V : Type} {ℓ N : Nat} (hN : 0 < N)
    {base : Fin (ℓ+1) → V} (hbase : Function.Injective base)
    {fiber : Fin (ℓ+1) → Fin N → V} (hfiber : ∀ j, Function.Injective (fiber j)) :
    (List.ofFn (expand hN base fiber)).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  have hh := expand_injective hN hbase hfiber he
  exact congrArg (fun z : Fin (ℓ*N+1) => z.val) hh

/-- Adjacent plus macros join at exactly the same diagonal vertex. -/
theorem plusMacros_stitch {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    plusMacro hN cycle i ⟨N,by omega⟩ =
      plusMacro hN cycle (successor hN i) ⟨0,by omega⟩ := by
  rw [plusMacro_end,plusMacro_start]

/-- Minus macros join in the opposite cyclic source order. -/
theorem minusMacros_stitch {V : Type} {N : Nat} (hN : 0 < N)
    (cycle : Fin N → V) (i : Fin N) :
    minusMacro hN cycle i ⟨N,by omega⟩ =
      minusMacro hN cycle (predecessor hN i) ⟨0,by omega⟩ := by
  rw [minusMacro_end,minusMacro_start]

/-- The j-th plus macro on a factor-compatible directed base edge starts at
that edge's source diagonal and ends at its target diagonal. This works even
when neighboring base edges belong to different Hamilton factors. -/
theorem compatible_macro_endpoints {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} {i : Fin N} {u v : V}
    (hu : cycle i = u) (hv : cycle (successor hN i) = v) :
    plusMacro hN cycle i ⟨0,by omega⟩ = (u,u) ∧
    plusMacro hN cycle i ⟨N,by omega⟩ = (v,v) := by
  constructor
  · rw [plusMacro_start,hu]
  · rw [plusMacro_end,hv]

/-- Every nonterminal column of the explicit plus macro is the whole vertex fiber. -/
theorem plus_macro_fiber {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hcycle : Function.Surjective cycle) (i : Fin N) (v : V) :
    ∃ r : Fin N, plusMacro hN cycle i r.castSucc = (cycle i,v) := by
  obtain ⟨j,hj⟩ := hcycle v
  obtain ⟨r,hr⟩ := backward_surjective hN i j
  refine ⟨r, ?_⟩
  have hh : r.val < N := r.isLt
  simp [plusMacro,hh,Fin.castSucc,Fin.castAdd,Fin.castLE,hr,hj]

/-- Every nonterminal row of the explicit minus macro is the whole vertex fiber. -/
theorem minus_macro_fiber {V : Type} {N : Nat} (hN : 0 < N)
    {cycle : Fin N → V} (hcycle : Function.Surjective cycle) (i : Fin N) (v : V) :
    ∃ r : Fin N, minusMacro hN cycle i r.castSucc = (v,cycle i) := by
  obtain ⟨j,hj⟩ := hcycle v
  obtain ⟨r,hr⟩ := forward_surjective hN i j
  refine ⟨r, ?_⟩
  have hh : r.val < N := r.isLt
  simp [minusMacro,hh,Fin.castSucc,Fin.castAdd,Fin.castLE,hr,hj]

#print axioms macroStep_adjacent
#print axioms plusVertex_injective
#print axioms expanded_list_nodup
#print axioms torus_macro_edge_partition
#print axioms expand_cyclic_injective
#print axioms successor_backward_step
end ErdePaths.SquareLift
