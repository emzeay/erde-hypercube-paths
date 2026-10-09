import Std

namespace ErdePaths

/-- Integers in `[0,2^n)` encode binary n-tuples, using least significant bit first. -/
abbrev Vertex (n : Nat) := Fin (2 ^ n)

/-- Exactly one of the n binary coordinates differs. -/
def Adjacent {n : Nat} (u v : Vertex n) : Prop :=
  ∃ d : Fin n, u.val.testBit d.val ≠ v.val.testBit d.val ∧
    ∀ i : Fin n, i ≠ d → u.val.testBit i.val = v.val.testBit i.val

instance {n : Nat} (u v : Vertex n) : Decidable (Adjacent u v) := by
  unfold Adjacent
  infer_instance

theorem adjacent_symm {n : Nat} {u v : Vertex n} (h : Adjacent u v) : Adjacent v u := by
  obtain ⟨d, hd, hi⟩ := h
  exact ⟨d, Ne.symm hd, fun i h => (hi i h).symm⟩

theorem adjacent_ne {n : Nat} {u v : Vertex n} (h : Adjacent u v) : u ≠ v := by
  rintro rfl
  obtain ⟨d, hd, _⟩ := h
  exact hd rfl

/-- Consecutive vertex pairs, before forgetting their orientation. -/
def steps {α : Type} (p : List α) : List (α × α) := p.zip p.tail

/-- Edge membership ignores orientation, as appropriate to the undirected cube. -/
def UsesEdge {n : Nat} (p : List (Vertex n)) (u v : Vertex n) : Prop :=
  (u, v) ∈ steps p ∨ (v, u) ∈ steps p

/-- Distinct vertices imply a simple path; its vertex count is edge count plus one. -/
def IsSimplePath {n : Nat} (ℓ : Nat) (p : List (Vertex n)) : Prop :=
  p.length = ℓ + 1 ∧ p.Nodup ∧ ∀ e ∈ steps p, Adjacent e.1 e.2

/-- A finite family of simple paths, with each undirected cube edge owned uniquely.
The explicit index list certifies finiteness. Repeated indices have no effect, since
this is an indexed family, and uniqueness is uniqueness of the index, not of a list occurrence.
Indices outside the list are irrelevant. Vertex sharing between paths is permitted. -/
def HasPathDecomposition (n ℓ : Nat) : Prop :=
  ∃ (ι : Type) (indices : List ι) (paths : ι → List (Vertex n)),
    (∀ i ∈ indices, IsSimplePath ℓ (paths i)) ∧
    ∀ u v : Vertex n, Adjacent u v →
      ∃ i, i ∈ indices ∧ UsesEdge (paths i) u v ∧
        ∀ j, j ∈ indices → UsesEdge (paths j) u v → j = i

/-- The full requested statement. This definition is a proposition, not an axiom. -/
def ErdeEvenHypercubeConjecture : Prop :=
  ∀ n ℓ : Nat, 2 ≤ n → n % 2 = 0 → 1 ≤ ℓ → ℓ < 2 ^ n →
    ℓ ∣ n * 2 ^ (n - 1) → HasPathDecomposition n ℓ

private def allVertices (n : Nat) : List (Vertex n) := List.ofFn id

private theorem mem_allVertices {n : Nat} (u : Vertex n) : u ∈ allVertices n := by
  simp [allVertices, List.mem_ofFn]

private def forwardEdges (n : Nat) : List (Vertex n × Vertex n) :=
  (allVertices n).flatMap fun u =>
    ((allVertices n).map fun v => (u, v)).filter fun e =>
      decide (e.1.val < e.2.val ∧ Adjacent e.1 e.2)

private theorem mem_forwardEdges {n : Nat} (u v : Vertex n) :
    (u, v) ∈ forwardEdges n ↔ u.val < v.val ∧ Adjacent u v := by
  simp [forwardEdges, List.mem_flatMap, List.mem_filter, List.mem_map,
    mem_allVertices]

/-- Every cube in every dimension decomposes into single-edge simple paths. -/
theorem length_one (n : Nat) : HasPathDecomposition n 1 := by
  refine ⟨Vertex n × Vertex n, forwardEdges n, fun e => [e.1, e.2], ?_, ?_⟩
  · intro e he
    have h := (mem_forwardEdges e.1 e.2).mp he
    refine ⟨rfl, ?_, ?_⟩
    · simp [List.nodup_cons, adjacent_ne h.2]
    · simpa [steps] using h.2
  · intro u v huv
    have hne := adjacent_ne huv
    have hval : u.val ≠ v.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hval with hlt | hgt
    · refine ⟨(u, v), (mem_forwardEdges u v).mpr ⟨hlt, huv⟩, ?_, ?_⟩
      · simp [UsesEdge, steps]
      · intro j hj hu
        have hjlt := ((mem_forwardEdges j.1 j.2).mp hj).1
        simp [UsesEdge, steps] at hu
        rcases hu with h | h
        · exact Prod.ext h.1.symm h.2.symm
        · have : j.1 = v ∧ j.2 = u := ⟨h.1.symm, h.2.symm⟩
          rcases this with ⟨h1, h2⟩
          rw [h1, h2] at hjlt
          omega
    · refine ⟨(v, u), (mem_forwardEdges v u).mpr ⟨hgt, adjacent_symm huv⟩, ?_, ?_⟩
      · simp [UsesEdge, steps]
      · intro j hj hu
        have hjlt := ((mem_forwardEdges j.1 j.2).mp hj).1
        simp [UsesEdge, steps] at hu
        rcases hu with h | h
        · have : j.1 = u ∧ j.2 = v := ⟨h.1.symm, h.2.symm⟩
          rcases this with ⟨h1, h2⟩
          rw [h1, h2] at hjlt
          omega
        · exact Prod.ext h.1.symm h.2.symm

#print axioms length_one
end ErdePaths
