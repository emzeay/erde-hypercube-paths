import ErdePaths.SourceClock

namespace ErdePaths.HamiltonScan

/-- The three nonzero rows of the two-bit cube. -/
inductive Row where
  | primary : Bool → Row
  | top : Row
  deriving DecidableEq

inductive Kind (k : Nat) where
  | ordinary : Kind k
  | lower : Fin k → Kind k
  | upper : Fin k → Kind k
  deriving DecidableEq

/-- Actual disjoint normalized matching endpoints and their finite lookup.
The lookup laws concern only endpoints, not any scan or its coverage. -/
structure Matching (N k : Nat) where
  lower : Fin k → Nat
  upper : Fin k → Nat
  kind : Nat → Kind k
  lower_kind : ∀ i, kind (lower i) = .lower i
  upper_kind : ∀ i, kind (upper i) = .upper i
  kind_lower : ∀ j i, kind j = .lower i → j = lower i
  kind_upper : ∀ j i, kind j = .upper i → j = upper i
  lower_pos : ∀ i, 0 < lower i
  ordered : ∀ i, lower i < upper i
  upper_bound : ∀ i, upper i < N-1

def block {N k} (M : Matching N k) (state : Nat → Bool) (j : Nat) :
    List (Nat × Row) :=
  match M.kind j with
  | .ordinary => [(j,.primary (state j)),(j,.top),(j,.primary (!(state j)))]
  | .upper _ => [(j,.primary (state j))]
  | .lower i =>
    if state j = state (M.upper i) then
      [(j,.primary (state j)),(j,.top),(M.upper i,.top),
       (M.upper i,.primary (!(state (M.upper i)))),(j,.primary (!(state j)))]
    else
      [(j,.primary (state j)),(M.upper i,.primary (state j)),
       (M.upper i,.top),(j,.top),(j,.primary (!(state j)))]

/-- Each emitted vertex has a unique emitting block, including deferred rows. -/
def owner {N k} (M : Matching N k) (state : Nat → Bool) (v : Nat × Row) : Nat :=
  match M.kind v.1 with
  | .upper i => if v.2 = .primary (state v.1) then v.1 else M.lower i
  | _ => v.1

theorem block_owner {N k} (M : Matching N k) (state : Nat → Bool) (j : Nat)
    (v : Nat × Row) (hv : v ∈ block M state j) : owner M state v = j := by
  unfold block at hv
  cases hk : M.kind j with
  | ordinary =>
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl <;> simp [owner,hk]
  | upper i =>
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v
    simp [owner,hk]
  | lower i =>
    have hj := M.kind_lower j i hk
    have hu := M.upper_kind i
    have hl := M.lower_kind i
    subst j
    by_cases he : state (M.lower i) = state (M.upper i)
    · simp only [hk,ite_eq_left he,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;>
        simp [owner,hl,hu]
    · simp only [hk,ite_eq_right he,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;>
        simp [owner,hl,hu,he]

theorem block_nodup {N k} (M : Matching N k) (state : Nat → Bool) (j : Nat) :
    (block M state j).Nodup := by
  unfold block
  cases hk : M.kind j with
  | ordinary => cases state j <;> simp
  | upper i => simp
  | lower i =>
    have hj := M.kind_lower j i hk
    have hne : j ≠ M.upper i := by have hh := M.ordered i; omega
    cases hs : state j <;> cases ht : state (M.upper i) <;>
      simp [ht,hne,Ne.symm hne]

theorem blocks_nodup {N k} (M : Matching N k) (state : Nat → Bool)
    (indices : List Nat) (hi : indices.Nodup) :
    (indices.flatMap (block M state)).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _; exact block_nodup M state j
  · apply hi.imp
    intro j l hjl v hv w hw he
    have ho := block_owner M state j v hv
    have hp := block_owner M state l w hw
    rw [he] at ho
    exact hjl (ho.symm.trans hp)

def middle (N : Nat) : List Nat := ((List.range (N-2)).map (·+1)).reverse

theorem middle_mem {N j : Nat} : j ∈ middle N ↔ 0<j ∧ j<N-1 := by
  simp only [middle,List.mem_reverse,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨a,ha,rfl⟩; omega
  · intro ⟨hp,hb⟩
    exact ⟨j-1,by omega,by omega⟩

theorem middle_nodup (N : Nat) : (middle N).Nodup := by
  unfold middle
  apply List.pairwise_reverse.mpr
  apply List.pairwise_map.mpr
  apply (List.nodup_range (n := N-2)).imp
  intro a b hab hba
  exact hab (by omega)

/-- Every nonzero row of every middle base vertex occurs, not merely a
cardinality count. -/
theorem middle_coverage {N k} (M : Matching N k) (state : Nat → Bool)
    (j : Nat) (row : Row) (hj : 0<j ∧ j<N-1) :
    (j,row) ∈ (middle N).flatMap (block M state) := by
  cases hk : M.kind j with
  | ordinary =>
    apply List.mem_flatMap.mpr
    refine ⟨j,middle_mem.mpr hj,?_⟩
    cases row with
    | top => simp [block,hk]
    | primary b => cases hs : state j <;> cases b <;> simp [block,hk,hs]
  | lower i =>
    apply List.mem_flatMap.mpr
    refine ⟨j,middle_mem.mpr hj,?_⟩
    cases row with
    | top => simp [block,hk]; split <;> simp
    | primary b =>
      cases hs : state j <;> cases ht : state (M.upper i) <;> cases b <;>
        simp [block,hk,hs,ht]
  | upper i =>
    have hjup := M.kind_upper j i hk
    by_cases he : row = .primary (state j)
    · apply List.mem_flatMap.mpr
      exact ⟨j,middle_mem.mpr hj,by simp [block,hk,he]⟩
    · apply List.mem_flatMap.mpr
      refine ⟨M.lower i,middle_mem.mpr ⟨M.lower_pos i,by
        have hlo := M.ordered i; have hup := M.upper_bound i; omega⟩,?_⟩
      have hl := M.lower_kind i
      subst j
      cases row with
      | top => simp [block,hl]; split <;> simp
      | primary b =>
        cases hs : state (M.lower i) <;> cases ht : state (M.upper i) <;>
          cases b <;> simp_all [block]

theorem block_middle {N k} (M : Matching N k) (state : Nat → Bool)
    (j : Nat) (hj : j ∈ middle N) (v : Nat × Row) (hv : v ∈ block M state j) :
    v.1 ∈ middle N := by
  unfold block at hv
  cases hk : M.kind j with
  | ordinary =>
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl | rfl <;> exact hj
  | upper i =>
    simp only [hk,List.mem_cons,List.not_mem_nil,or_false] at hv
    subst v; exact hj
  | lower i =>
    have hu : M.upper i ∈ middle N := middle_mem.mpr ⟨by
      have hlo := M.lower_pos i; have ho := M.ordered i; omega,M.upper_bound i⟩
    by_cases he : state j = state (M.upper i)
    · simp only [hk,ite_eq_left he,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption
    · simp only [hk,ite_eq_right he,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem middle_exact {N k} (M : Matching N k) (state : Nat → Bool)
    (v : Nat × Row) : v ∈ (middle N).flatMap (block M state) ↔
      0<v.1 ∧ v.1<N-1 := by
  constructor
  · intro hv
    obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
    exact middle_mem.mp (block_middle M state j hj v hv)
  · intro hv; exact middle_coverage M state v.1 v.2 hv

def word {N k} (M : Matching N k) (state : Nat → Bool) : List (Nat × Row) :=
  [(N-1,.primary false)] ++ (middle N).flatMap (block M state) ++
    [(0,.primary (state 0))]

theorem word_exact {N k} (M : Matching N k) (state : Nat → Bool)
    (v : Nat × Row) : v ∈ word M state ↔
      v = (N-1,.primary false) ∨ (0<v.1 ∧ v.1<N-1) ∨
        v = (0,.primary (state 0)) := by
  simp only [word,List.mem_append,List.mem_singleton,middle_exact,or_assoc]

theorem word_nodup {N k} (M : Matching N k) (state : Nat → Bool) (hN : 2≤N) :
    (word M state).Nodup := by
  have hm := blocks_nodup M state (middle N) (middle_nodup N)
  have htail : ((middle N).flatMap (block M state) ++ [(0,Row.primary (state 0))]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hm,by simp,?_⟩
    intro a ha b hb he
    have ha := (middle_exact M state a).mp ha
    simp at hb
    rw [hb] at he
    have := congrArg Prod.fst he
    simp at this
    omega
  change ((N-1,.primary false) ::
    ((middle N).flatMap (block M state) ++ [(0,.primary (state 0))])).Nodup
  apply List.nodup_cons.mpr
  refine ⟨?_,htail⟩
  intro hm
  rcases List.mem_append.mp hm with hm | hb
  · have := (middle_exact M state _).mp hm
    omega
  · simp only [List.mem_singleton,Prod.mk.injEq] at hb
    omega

/-- Descending scan state, indexed by the number of already processed middle
vertices. This is a finite primitive recursion, not a supplied invariant. -/
def stateAux {N k} (M : Matching N k) : Nat → Bool
  | 0 => false
  | n+1 => match M.kind (N-2-n) with
    | .upper _ => stateAux M n
    | _ => !(stateAux M n)

def state {N k} (M : Matching N k) (j : Nat) : Bool := stateAux M (N-2-j)

theorem state_initial {N k} (M : Matching N k) : state M (N-2)=false := by
  simp [state,stateAux]

theorem state_step {N k} (M : Matching N k) (j : Nat) (hj : 1≤j ∧ j≤N-2) :
    state M (j-1) = match M.kind j with
      | .upper _ => state M j
      | _ => !(state M j) := by
  have hd : N-2-(j-1) = (N-2-j)+1 := by omega
  have hi : N-2-(N-2-j)=j := by omega
  unfold state
  rw [hd,stateAux,hi]

theorem block_nonempty {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat) :
    block M s j ≠ [] := by
  unfold block
  cases M.kind j <;> simp
  split <;> simp

theorem block_head {N k} (M : Matching N k) (s : Nat → Bool) (j : Nat) :
    (block M s j).head? = some (j,.primary (s j)) := by
  unfold block
  cases M.kind j <;> simp
  split <;> simp

/-- The actual last vertex of a block has precisely the outgoing state; thus
adjacent scan blocks join at successive base indices in the same row. -/
theorem block_last {N k} (M : Matching N k) (j : Nat) (hj : 1≤j ∧ j≤N-2) :
    (block M (state M) j).getLast? = some (j,.primary (state M (j-1))) := by
  rw [state_step M j hj]
  unfold block
  cases M.kind j <;> simp
  split <;> simp

def toggleCount {N k} (M : Matching N k) : Nat → Nat
  | 0 => 0
  | n+1 => match M.kind (N-2-n) with
    | .upper _ => toggleCount M n
    | _ => toggleCount M n + 1

/-- The recursive state is exactly the parity of the number of toggles. -/
theorem stateAux_parity {N k} (M : Matching N k) (n : Nat) :
    stateAux M n = decide (toggleCount M n % 2 = 1) := by
  induction n with
  | zero => simp [stateAux,toggleCount]
  | succ n ih =>
    have hp : toggleCount M n % 2 < 2 := Nat.mod_lt _ (by omega)
    have ht : (!(decide (toggleCount M n % 2 = 1))) =
        decide ((toggleCount M n + 1) % 2 = 1) := by
      by_cases h : toggleCount M n % 2 = 0
      · simp [Nat.add_mod,h]
      · have h1 : toggleCount M n % 2 = 1 := by omega
        simp [Nat.add_mod,h1]
    cases hk : M.kind (N-2-n) <;>
      simp only [stateAux,toggleCount,hk,ih] <;> first | exact ht | rfl

def isUpper {k} : Kind k → Bool
  | .upper _ => true
  | _ => false

/-- The parity count really enumerates previously processed indices. -/
theorem toggleCount_filter {N k} (M : Matching N k) (n : Nat) :
    toggleCount M n = ((List.range n).filter fun a =>
      !(isUpper (M.kind (N-2-a)))).length := by
  induction n with
  | zero => simp [toggleCount]
  | succ n ih =>
    rw [List.range_succ,List.filter_append,List.length_append,← ih]
    cases hk : M.kind (N-2-n) <;> simp [toggleCount,isUpper,hk]

def fullBlock (j : Nat) : List (Nat × Row) :=
  [(j,.primary false),(j,.primary true),(j,.top)]

theorem fullBlock_exact (v : Nat × Row) (j : Nat) :
    v ∈ fullBlock j ↔ v.1=j := by
  cases v with
  | mk a r => cases r with
    | top => simp [fullBlock]
    | primary b => cases b <;> simp [fullBlock]

theorem fullBlocks_nodup (indices : List Nat) (hn : indices.Nodup) :
    (indices.flatMap fullBlock).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _; simp [fullBlock]
  · apply hn.imp
    intro j l hjl v hv w hw he
    have hv := (fullBlock_exact v j).mp hv
    have hw := (fullBlock_exact w l).mp hw
    have hh := congrArg Prod.fst he
    exact hjl (by omega)

theorem blocks_perm_full {N k} (M : Matching N k) (s : Nat → Bool) :
    ((middle N).flatMap (block M s)).Perm ((middle N).flatMap fullBlock) := by
  apply (List.perm_ext_iff_of_nodup
    (blocks_nodup M s (middle N) (middle_nodup N))
    (fullBlocks_nodup (middle N) (middle_nodup N))).mpr
  intro v
  rw [middle_exact]
  constructor
  · intro hv; exact List.mem_flatMap.mpr ⟨v.1,middle_mem.mpr hv,
      (fullBlock_exact v v.1).mpr rfl⟩
  · intro hv
    obtain ⟨j,hj,hv⟩ := List.mem_flatMap.mp hv
    have hv := (fullBlock_exact v j).mp hv
    rw [hv]
    exact middle_mem.mp hj

theorem fullBlocks_length (indices : List Nat) :
    (indices.flatMap fullBlock).length = 3*indices.length := by
  induction indices with
  | nil => simp
  | cons j l ih => simp [fullBlock,ih]; omega

theorem word_length {N k} (M : Matching N k) (s : Nat → Bool) (hN : 2≤N) :
    (word M s).length = 3*N-4 := by
  have hp := (blocks_perm_full M s).length_eq
  rw [fullBlocks_length] at hp
  have hm : (middle N).length=N-2 := by simp [middle]
  rw [hm] at hp
  simp only [word,List.length_append,List.length_cons,List.length_nil]
  omega

def RowAdjacent (a b : Row) : Prop :=
  (a = .top ∧ ∃ s, b = .primary s) ∨
    (b = .top ∧ ∃ s, a = .primary s)

def GridAdjacent (R : Nat → Nat → Prop) (v w : Nat × Row) : Prop :=
  (v.1=w.1 ∧ RowAdjacent v.2 w.2) ∨ (v.2=w.2 ∧ R v.1 w.1)

def Chain {V : Type} (R : V → V → Prop) : List V → Prop
  | [] => True
  | [_] => True
  | a::b::l => R a b ∧ Chain R (b::l)

/-- Every internal block step is an actual vertical row edge or the selected
matching edge, with its orientation handled by symmetry. -/
theorem block_chain {N k} (M : Matching N k) (s : Nat → Bool)
    (R : Nat → Nat → Prop) (hsym : ∀ a b, R a b → R b a)
    (hselected : ∀ i, R (M.lower i) (M.upper i)) (j : Nat) :
    Chain (GridAdjacent R) (block M s j) := by
  unfold block
  cases hk : M.kind j with
  | ordinary => cases s j <;> simp [Chain,GridAdjacent,RowAdjacent]
  | upper i => trivial
  | lower i =>
    have hj := M.kind_lower j i hk
    have hu := hselected i
    have hv := hsym _ _ hu
    cases hs : s j <;> cases ht : s (M.upper i) <;>
      simp [ht,Chain,GridAdjacent,RowAdjacent,hj,hu,hv]

/-- Row interpretation uses precisely numeric rows 1,2,3 of Q₂. -/
def rowIndex : Row → Fin 4
  | .primary false => ⟨1,by decide⟩
  | .primary true => ⟨2,by decide⟩
  | .top => ⟨3,by decide⟩

theorem rowIndex_injective : Function.Injective rowIndex := by
  intro a b hab
  cases a with
  | top => cases b with
    | top => rfl
    | primary q => cases q <;> simp [rowIndex] at hab
  | primary p => cases b with
    | top => cases p <;> simp [rowIndex] at hab
    | primary q => cases p <;> cases q <;> simp_all [rowIndex]

theorem word_base_bound {N k} (M : Matching N k) (s : Nat → Bool)
    (hN : 2≤N) (v : Nat × Row) (hv : v ∈ word M s) : v.1<N := by
  rcases (word_exact M s v).mp hv with hv | hv | hv
  · rw [hv]; omega
  · omega
  · rw [hv]; omega

/-- Transport to actual parent-cycle vertices does not lose simplicity.
Only injectivity on the actual bounded base coordinates is required. -/
theorem word_transport_nodup {N k V} (M : Matching N k) (s : Nat → Bool)
    (hN : 2≤N) (f : Nat → V)
    (hf : ∀ a b, a<N → b<N → f a=f b → a=b) :
    ((word M s).map fun v => (f v.1,rowIndex v.2)).Nodup := by
  apply List.pairwise_map.mpr
  apply (word_nodup M s hN).imp_of_mem
  intro v w hv hw hne he
  have hbase := hf v.1 w.1 (word_base_bound M s hN v hv)
    (word_base_bound M s hN w hw) (congrArg Prod.fst he)
  have hrow := rowIndex_injective (congrArg Prod.snd he)
  exact hne (Prod.ext hbase hrow)

theorem block_boundary_edge {N k} (M : Matching N k)
    (R : Nat → Nat → Prop) (j : Nat) (h : R j (j-1)) :
    GridAdjacent R (j,.primary (state M (j-1)))
      (j-1,.primary (state M (j-1))) := Or.inr ⟨rfl,h⟩

#print axioms word_nodup
#print axioms word_exact
#print axioms state_step
#print axioms block_last
#print axioms word_length
#print axioms block_chain

end ErdePaths.HamiltonScan
