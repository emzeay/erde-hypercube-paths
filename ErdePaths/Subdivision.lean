import ErdePaths.Basic

namespace ErdePaths

/-- Consecutive overlapping vertex windows; edge intervals do not overlap. -/
def segment {α : Type} (p : List α) (ℓ j : Nat) : List α :=
  (p.drop (j * ℓ)).take (ℓ + 1)

theorem steps_drop {α : Type} (p : List α) (s : Nat) :
    steps (p.drop s) = (steps p).drop s := by
  induction s generalizing p with
  | zero => simp [steps]
  | succ s ih =>
    cases p with
    | nil => simp [steps]
    | cons a p =>
      cases p with
      | nil => simp [steps]
      | cons b p => simpa [steps] using ih (b :: p)

theorem steps_take {α : Type} (p : List α) (t : Nat) :
    steps (p.take (t + 1)) = (steps p).take t := by
  induction t generalizing p with
  | zero => cases p <;> simp [steps]
  | succ t ih =>
    cases p with
    | nil => simp [steps]
    | cons a p =>
      cases p with
      | nil => simp [steps]
      | cons b p => simpa [steps] using congrArg (List.cons (a,b)) (ih (b :: p))

theorem steps_segment {α : Type} (p : List α) (ℓ j : Nat) :
    steps (segment p ℓ j) = ((steps p).drop (j * ℓ)).take ℓ := by
  rw [segment, steps_take, steps_drop]

/-- All vertices of a segment come from the original path; boundary vertices may overlap. -/
theorem segment_simple {n L ℓ j : Nat} {p : List (Vertex n)}
    (hp : IsSimplePath L p) (hj : (j + 1) * ℓ ≤ L) :
    IsSimplePath ℓ (segment p ℓ j) := by
  obtain ⟨hlen, hnd, hadj⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · simp only [segment, List.length_take, List.length_drop, hlen]
    rw [Nat.min_eq_left]
    have hm : (j + 1) * ℓ = j * ℓ + ℓ := by simp [Nat.add_mul]
    omega
  · exact List.Pairwise.take (List.Pairwise.drop hnd)
  · intro e he
    rw [steps_segment] at he
    exact hadj e (List.mem_of_mem_drop (List.mem_of_mem_take he))

/-- An undirected edge occurring at a specified consecutive position. -/
def EdgeAt {α : Type} (p : List α) (t : Nat) (u v : α) : Prop :=
  ∃ h : t + 1 < p.length,
    (p[t]'(by omega) = u ∧ p[t+1]'h = v) ∨
    (p[t]'(by omega) = v ∧ p[t+1]'h = u)

theorem usesEdge_iff_position {n : Nat} (p : List (Vertex n)) (u v : Vertex n) :
    UsesEdge p u v ↔ ∃ t, EdgeAt p t u v := by
  simp only [UsesEdge, steps, List.mem_iff_getElem, List.length_zip, List.length_tail,
    List.getElem_zip, List.getElem_tail]
  constructor
  · rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨t, by refine ⟨by omega, ?_⟩; left; simpa [Prod.mk.injEq] using he⟩
    · exact ⟨t, by refine ⟨by omega, ?_⟩; right; simpa [Prod.mk.injEq] using he⟩
  · rintro ⟨t, ht, he | he⟩
    · left; exact ⟨t, by omega, by simpa [Prod.mk.injEq] using he⟩
    · right; exact ⟨t, by omega, by simpa [Prod.mk.injEq] using he⟩

theorem edgeAt_unique {α : Type} {p : List α} (hp : p.Nodup) {s t : Nat} {u v : α}
    (hs : EdgeAt p s u v) (ht : EdgeAt p t u v) : s = t := by
  obtain ⟨hs, hs⟩ := hs
  obtain ⟨ht, ht⟩ := ht
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact hp.getElem_inj.mp (hs.1.trans ht.1.symm)
  · have h1 := hp.getElem_inj.mp (hs.1.trans ht.2.symm)
    have h2 := hp.getElem_inj.mp (hs.2.trans ht.1.symm)
    omega
  · have h1 := hp.getElem_inj.mp (hs.1.trans ht.2.symm)
    have h2 := hp.getElem_inj.mp (hs.2.trans ht.1.symm)
    omega
  · exact hp.getElem_inj.mp (hs.1.trans ht.1.symm)

 theorem edgeAt_segment_iff {n L ℓ j t : Nat} {p : List (Vertex n)}
    (hp : IsSimplePath L p) (hj : (j + 1) * ℓ ≤ L) (u v : Vertex n) :
    EdgeAt (segment p ℓ j) t u v ↔ t < ℓ ∧ EdgeAt p (j * ℓ + t) u v := by
  have hlen := (segment_simple hp hj).1
  have hplen := hp.1
  have hm : (j + 1) * ℓ = j * ℓ + ℓ := by simp [Nat.add_mul]
  constructor
  · rintro ⟨ht, he⟩
    have htl : t < ℓ := by omega
    refine ⟨htl, ⟨by omega, ?_⟩⟩
    simpa [segment, List.getElem_take, List.getElem_drop, Nat.add_assoc] using he
  · rintro ⟨htl, ht, he⟩
    refine ⟨by omega, ?_⟩
    simpa [segment, List.getElem_take, List.getElem_drop, Nat.add_assoc] using he

/-- Subdivision preserves all edges and assigns each one to a unique segment. -/
theorem segment_edge_partition {n ℓ k : Nat} {p : List (Vertex n)}
    (hp : IsSimplePath (ℓ * k) p) (hℓ : 0 < ℓ) (u v : Vertex n)
    (huv : UsesEdge p u v) :
    ∃ j, j < k ∧ UsesEdge (segment p ℓ j) u v ∧
      ∀ j', j' < k → UsesEdge (segment p ℓ j') u v → j' = j := by
  obtain ⟨t, ht⟩ := (usesEdge_iff_position p u v).mp huv
  have htbound : t < ℓ * k := by obtain ⟨h, _⟩ := ht; have := hp.1; omega
  have hj : t / ℓ < k := Nat.div_lt_of_lt_mul htbound
  have hw (j : Nat) (hj : j < k) : (j + 1) * ℓ ≤ ℓ * k := by
    have := Nat.mul_le_mul_left ℓ (by omega : j+1 ≤ k)
    simpa [Nat.mul_comm] using this
  have hrem : t % ℓ < ℓ := Nat.mod_lt _ hℓ
  have heq : t / ℓ * ℓ + t % ℓ = t := by simpa [Nat.mul_comm] using Nat.div_add_mod t ℓ
  refine ⟨t / ℓ, hj, ?_, ?_⟩
  · apply (usesEdge_iff_position _ _ _).mpr
    refine ⟨t % ℓ, (edgeAt_segment_iff hp (hw _ hj) u v).mpr ⟨hrem, ?_⟩⟩
    simpa [heq] using ht
  · intro j' hj' he'
    obtain ⟨t', ht'⟩ := (usesEdge_iff_position _ _ _).mp he'
    obtain ⟨hb', ht'⟩ := (edgeAt_segment_iff hp (hw _ hj') u v).mp ht'
    have hh := edgeAt_unique hp.2.1 ht' ht
    have hdiv := Nat.div_eq_of_lt hb'
    have hcalc : (j' * ℓ + t') / ℓ = j' := by
      rw [Nat.mul_comm j' ℓ, Nat.mul_add_div hℓ, hdiv, Nat.add_zero]
    rw [hh] at hcalc
    exact hcalc.symm

 theorem usesEdge_segment_implies {n : Nat} (p : List (Vertex n)) (ℓ j : Nat)
    (u v : Vertex n) (h : UsesEdge (segment p ℓ j) u v) : UsesEdge p u v := by
  rcases h with h | h
  · left
    rw [steps_segment] at h
    exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  · right
    rw [steps_segment] at h
    exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- Every divisor of a positive path length is obtained by cutting consecutive
vertex windows, with the shared endpoints retained in both neighboring paths.
This theorem also handles L=0: an edge-free cube has an empty refinement. -/
theorem subdivision {n L ℓ : Nat} (h : HasPathDecomposition n L)
    (hℓ : 1 ≤ ℓ) (hdiv : ℓ ∣ L) : HasPathDecomposition n ℓ := by
  obtain ⟨k, rfl⟩ := hdiv
  obtain ⟨ι, indices, paths, hpaths, hcover⟩ := h
  let newIndices : List (ι × Nat) := indices.flatMap fun i => (List.range k).map (i, ·)
  have hmem (i : ι) (j : Nat) : (i,j) ∈ newIndices ↔ i ∈ indices ∧ j < k := by
    simp [newIndices, List.mem_flatMap, List.mem_map]
  have hw (j : Nat) (hj : j < k) : (j + 1) * ℓ ≤ ℓ * k := by
    have := Nat.mul_le_mul_left ℓ (by omega : j+1 ≤ k)
    simpa [Nat.mul_comm] using this
  refine ⟨ι × Nat, newIndices, fun a => segment (paths a.1) ℓ a.2, ?_, ?_⟩
  · intro a ha
    obtain ⟨hi,hj⟩ := (hmem a.1 a.2).mp ha
    exact segment_simple (hpaths a.1 hi) (hw a.2 hj)
  · intro u v huv
    obtain ⟨i, hi, he, huniq⟩ := hcover u v huv
    obtain ⟨j, hj, hseg, hseguniq⟩ := segment_edge_partition (hpaths i hi) (by omega) u v he
    refine ⟨(i,j), (hmem i j).mpr ⟨hi,hj⟩, hseg, ?_⟩
    intro a ha hea
    obtain ⟨hai,haj⟩ := (hmem a.1 a.2).mp ha
    have hieq : a.1 = i := huniq a.1 hai (usesEdge_segment_implies _ ℓ a.2 u v hea)
    have hjeq : a.2 = j := by
      apply hseguniq a.2 haj
      simpa [hieq] using hea
    exact Prod.ext hieq hjeq

#print axioms subdivision
end ErdePaths
