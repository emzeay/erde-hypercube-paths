import ErdePaths.NoncrossingMatch

namespace ErdePaths.ChordGraph
open NoncrossingMatch

/-- Brackets are edges; list positions distinguish parallel physical edges. -/
def chords {O : Type} {κ : O → Bool} : Forest O κ → List (O × O)
  | .empty => []
  | .concat u v => chords u ++ chords v
  | .bracket x u y _ => (x,y) :: chords u

theorem chords_opposite {O : Type} {κ : O → Bool} (F : Forest O κ)
    (e : O × O) (he : e ∈ chords F) : κ e.1 ≠ κ e.2 := by
  induction F with
  | empty => simp [chords] at he
  | concat u v ihu ihv =>
    rcases List.mem_append.mp he with h | h
    · exact ihu h
    · exact ihv h
  | bracket x u y h ih =>
    rcases List.mem_cons.mp he with he | he
    · subst e; exact h
    · exact ih he

def incident {O V : Type} [DecidableEq V] (mark : O → V) (v : V) (e : O × O) : Bool :=
  decide (mark e.1 = v ∨ mark e.2 = v)

/-- Physical incidence counts exactly the original marked endpoint occurrences.
Opposite parity excludes loops, so Boolean incidence never loses a double endpoint. -/
theorem incidence_count {O V : Type} [DecidableEq V] (χ : V → Bool) (mark : O → V)
    (F : Forest O (fun o => χ (mark o))) (v : V) :
    (chords F).countP (incident mark v) =
      F.flatten.countP (fun o => decide (mark o = v)) := by
  induction F with
  | empty => rfl
  | concat u w ihu ihw =>
    simp only [chords, Forest.flatten, List.countP_append, ihu, ihw]
  | bracket x u y h ih =>
    have hxy : mark x ≠ mark y := fun he => h (congrArg χ he)
    simp only [chords, Forest.flatten, List.countP_cons, List.countP_append,
      List.countP_nil, ih]
    by_cases hx : mark x = v <;> by_cases hy : mark y = v
    · exact False.elim (hxy (hx.trans hy.symm))
    all_goals simp [incident, hx, hy] <;> omega

/-- Each position in a position forest is incident to exactly one bracket occurrence. -/
theorem position_once {n : Nat} (κ : Fin n → Bool) (F : Forest (Fin n) κ)
    (hf : F.flatten = List.finRange n) (o : Fin n) :
    (chords F).countP (incident id o) = 1 := by
  have h := incidence_count κ id F o
  rw [hf] at h
  have hc := (List.nodup_finRange n).count (a := o)
  simp only [List.mem_finRange, ite_true, List.count_eq_countP] at hc
  have hp : (fun z : Fin n => decide (z = o)) = (fun z => z == o) := by
    funext z; apply Bool.eq_iff_iff.mpr; simp
  simp only [id_eq] at h
  rw [hp] at h
  exact h.trans hc

/-- Exact unique edge *position*, rather than a possibly repeated physical pair. -/
theorem position_unique_edge {n : Nat} (κ : Fin n → Bool) (F : Forest (Fin n) κ)
    (hf : F.flatten = List.finRange n) (o : Fin n) :
    ∃ j : Fin (chords F).length, incident id o (chords F)[j] = true ∧
      ∀ k, incident id o (chords F)[k] = true → k = j := by
  have hm : (List.finRange (chords F).length).map (fun j => (chords F)[j]) = chords F := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  have hc := congrArg (List.countP (incident id o)) hm
  rw [List.countP_map, position_once κ F hf o] at hc
  rw [List.countP_eq_length_filter] at hc
  obtain ⟨j,hj⟩ := List.length_eq_one_iff.mp hc
  refine ⟨j,?_,?_⟩
  · have hjm : j ∈ (List.finRange (chords F).length).filter
        ((incident id o) ∘ (fun j => (chords F)[j])) := by rw [hj]; simp
    exact (List.mem_filter.mp hjm).2
  · intro k hk
    have hkm : k ∈ (List.finRange (chords F).length).filter
        ((incident id o) ∘ (fun j => (chords F)[j])) :=
      List.mem_filter.mpr ⟨by simp, hk⟩
    rw [hj] at hkm
    simpa using hkm

/-- A regular bipartite multigraph represented by distinct edge indices.
No perfect matching or edge coloring is built into this definition. -/
structure RegularChordGraph (V : Type) [DecidableEq V] (χ : V → Bool) (b : Nat) where
  Edge : Type
  edges : List Edge
  distinct : edges.Nodup
  ends : Edge → V × V
  opposite : ∀ e ∈ edges, χ (ends e).1 ≠ χ (ends e).2
  regular : ∀ v, edges.countP (fun e => decide ((ends e).1 = v ∨ (ends e).2 = v)) = b

/-- Actual marks, before any pairing or coloring is chosen. -/
structure Marks (V : Type) [DecidableEq V] (χ : V → Bool) (m b : Nat) where
  word : Fin m → List V
  balanced : ∀ i, Balanced χ (word i)
  multiplicity : ∀ v,
    ((List.finRange m).map (fun i => (word i).countP (fun x => decide (x = v)))).sum = b

noncomputable def Marks.forest {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (i : Fin m) :
    Forest (Fin (M.word i).length) (fun o => χ (M.word i)[o]) :=
  Classical.choose (exists_position_forest χ (M.word i) (M.balanced i))

theorem Marks.forest_flatten {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (i : Fin m) :
    (M.forest i).flatten = List.finRange (M.word i).length :=
  Classical.choose_spec (exists_position_forest χ (M.word i) (M.balanced i))

/-- Family index plus bracket index, preserving all parallel edges. -/
abbrev Marks.Edge {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) := (i : Fin m) × Fin (chords (M.forest i)).length

noncomputable def Marks.edges {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) : List M.Edge :=
  (List.finRange m).flatMap (fun i =>
    (List.finRange (chords (M.forest i)).length).map (fun j => ⟨i,j⟩))

noncomputable def Marks.ends {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (e : M.Edge) : V × V :=
  let p := (chords (M.forest e.1))[e.2]
  ((M.word e.1)[p.1], (M.word e.1)[p.2])

theorem Marks.edges_complete {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (e : M.Edge) : e ∈ M.edges := by
  apply List.mem_flatMap.mpr
  refine ⟨e.1, by simp, ?_⟩
  apply List.mem_map.mpr
  exact ⟨e.2, by simp, rfl⟩

theorem Marks.opposite {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (e : M.Edge) : χ (M.ends e).1 ≠ χ (M.ends e).2 :=
  chords_opposite (M.forest e.1) _ (List.getElem_mem e.2.isLt)

theorem Marks.loop_free {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (e : M.Edge) : (M.ends e).1 ≠ (M.ends e).2 :=
  fun he => M.opposite e (congrArg χ he)

/-- The occurrence-level unique owner remains available before physical vertices
are identified; multiplicities never identify two bracket indices. -/
theorem Marks.occurrence_unique {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (i : Fin m) (o : Fin (M.word i).length) :
    ∃ j : Fin (chords (M.forest i)).length,
      incident id o (chords (M.forest i))[j] = true ∧
      ∀ k, incident id o (chords (M.forest i))[k] = true → k = j :=
  position_unique_edge _ (M.forest i) (M.forest_flatten i) o

theorem Marks.regular {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (v : V) :
    M.edges.countP (fun e => decide ((M.ends e).1 = v ∨ (M.ends e).2 = v)) = b := by
  rw [Marks.edges, List.countP_flatMap]
  have hi (i : Fin m) :
      ((List.finRange (chords (M.forest i)).length).map (fun j => (⟨i,j⟩ : M.Edge))).countP
        (fun e => decide ((M.ends e).1 = v ∨ (M.ends e).2 = v)) =
      (M.word i).countP (fun x => decide (x = v)) := by
    rw [List.countP_map]
    have hm : (List.finRange (chords (M.forest i)).length).map
        (fun j => (chords (M.forest i))[j]) = chords (M.forest i) := by
      simp [List.finRange, List.map_ofFn, Function.comp_def]
    have hc := incidence_count χ (fun o => (M.word i)[o]) (M.forest i) v
    rw [M.forest_flatten] at hc
    have hw : (List.finRange (M.word i).length).map (fun o => (M.word i)[o]) = M.word i := by
      simp [List.finRange, List.map_ofFn, Function.comp_def]
    have hwc := congrArg (List.countP (fun x => decide (x = v))) hw
    rw [List.countP_map] at hwc
    have hmc := congrArg (List.countP (incident (fun o => (M.word i)[o]) v)) hm
    rw [List.countP_map] at hmc
    exact hmc.trans (hc.trans hwc)
  have he : (List.countP (fun e => decide ((M.ends e).1 = v ∨ (M.ends e).2 = v)) ∘
      (fun i => (List.finRange (chords (M.forest i)).length).map (fun j => (⟨i,j⟩ : M.Edge)))) =
      (fun i => (M.word i).countP (fun x => decide (x = v))) := by
    funext i; exact hi i
  rw [he]
  exact M.multiplicity v

theorem Marks.edges_distinct {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) : M.edges.Nodup := by
  unfold Marks.edges
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (S := fun j k => (⟨i,j⟩ : M.Edge) ≠ ⟨i,k⟩)
      (fun h he => h (by cases he; rfl)) (List.nodup_finRange _)
  · have hp := List.nodup_finRange m
    refine List.Pairwise.imp (S := fun i j => ∀ (x : M.Edge),
      x ∈ (List.finRange (chords (M.forest i)).length).map (fun k => ⟨i,k⟩) →
      ∀ (y : M.Edge), y ∈ (List.finRange (chords (M.forest j)).length).map (fun k => ⟨j,k⟩) →
      x ≠ y) ?_ hp
    intro i j h x hx y hy he
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨l,_,rfl⟩ := List.mem_map.mp hy
    exact h (congrArg Sigma.fst he)

noncomputable def Marks.graph {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) : RegularChordGraph V χ b where
  Edge := M.Edge
  edges := M.edges
  distinct := M.edges_distinct
  ends := M.ends
  opposite := fun e _ => M.opposite e
  regular := M.regular

#print axioms position_unique_edge
#print axioms position_once
#print axioms Marks.regular
#print axioms Marks.graph
end ErdePaths.ChordGraph
