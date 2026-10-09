import Std

namespace ErdePaths.HallColor

/-- Finite bipartite multigraph. Edge identities are independent of endpoint pairs. -/
structure Bipartite (L R : Nat) where
  Edge : Type
  edges : List Edge
  distinct : edges.Nodup
  left : Edge → Fin L
  right : Edge → Fin R

def Bipartite.Regular {L R : Nat} (G : Bipartite L R) (b : Nat) : Prop :=
  (∀ x, G.edges.countP (fun e => decide (G.left e = x)) = b) ∧
  (∀ y, G.edges.countP (fun e => decide (G.right e = y)) = b)

/-- Actual neighboring right vertices of a left subset. -/
def Bipartite.neighbors {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) : List (Fin R) :=
  (List.finRange R).filter (fun y => decide (∃ e ∈ G.edges, G.left e ∈ A ∧ G.right e = y))

/-- Finite edge lists retain all parallel identities in double counting. -/
theorem countP_disjoint {E : Type} (es : List E) (p q : E → Bool)
    (h : ∀ e ∈ es, ¬(p e = true ∧ q e = true)) :
    es.countP (fun e => p e || q e) = es.countP p + es.countP q := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have he := h e (by simp)
    have hi := ih (fun e he => h e (by simp [he]))
    simp only [List.countP_cons, hi]
    cases hp : p e <;> cases hq : q e <;> simp_all <;> omega

theorem countP_mono {E : Type} (es : List E) (p q : E → Bool)
    (h : ∀ e ∈ es, p e = true → q e = true) : es.countP p ≤ es.countP q := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    have hi := ih (fun e he => h e (by simp [he]))
    have he := h e (by simp)
    simp only [List.countP_cons]
    cases hp : p e <;> cases hq : q e <;> simp_all <;> omega

/-- Fiber counts over a duplicate-free vertex subset equal its incident edge count. -/
theorem fiber_sum {E V : Type} [DecidableEq V] (es : List E) (f : E → V)
    (A : List V) (ha : A.Nodup) :
    (A.map (fun x => es.countP (fun e => decide (f e = x)))).sum =
      es.countP (fun e => decide (f e ∈ A)) := by
  induction A with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.nodup_cons.mp ha
    have hd := countP_disjoint es (fun e => decide (f e = x))
      (fun e => decide (f e ∈ xs)) (by
        intro e _ he
        have he1 : f e = x := of_decide_eq_true he.1
        have he2 : f e ∈ xs := of_decide_eq_true he.2
        exact hx (he1 ▸ he2))
    have he : (fun e => decide (f e ∈ x::xs)) =
        (fun e => decide (f e = x) || decide (f e ∈ xs)) := by
      funext e; apply Bool.eq_iff_iff.mpr; simp
    simp only [List.map_cons, List.sum_cons, ih hxs, he, hd]

theorem constant_sum {V : Type} (A : List V) (f : V → Nat) (b : Nat)
    (h : ∀ x ∈ A, f x = b) : (A.map f).sum = b * A.length := by
  induction A with
  | nil => simp
  | cons x xs ih =>
    have hi := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, h x (by simp), hi, Nat.mul_succ]
    omega

theorem Bipartite.subset_degree {L R : Nat} (G : Bipartite L R) (b : Nat)
    (hr : G.Regular b) (A : List (Fin L)) (ha : A.Nodup) :
    G.edges.countP (fun e => decide (G.left e ∈ A)) = b * A.length := by
  rw [←fiber_sum G.edges G.left A ha]
  exact constant_sum A _ b (fun x _ => hr.1 x)

theorem Bipartite.neighbors_distinct {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) :
    (G.neighbors A).Nodup := by
  exact (List.nodup_finRange R).filter _

/-- Hall's inequality, derived from regularity rather than postulated. -/
theorem Bipartite.hall {L R : Nat} (G : Bipartite L R) (b : Nat)
    (hb : 0 < b) (hr : G.Regular b) (A : List (Fin L)) (ha : A.Nodup) :
    A.length ≤ (G.neighbors A).length := by
  have hl := G.subset_degree b hr A ha
  have hrn : G.edges.countP (fun e => decide (G.right e ∈ G.neighbors A)) =
      b * (G.neighbors A).length := by
    rw [←fiber_sum G.edges G.right (G.neighbors A) (G.neighbors_distinct A)]
    exact constant_sum _ _ b (fun y _ => hr.2 y)
  have hm := countP_mono G.edges (fun e => decide (G.left e ∈ A))
    (fun e => decide (G.right e ∈ G.neighbors A)) (by
      intro e he hl
      apply decide_eq_true
      apply List.mem_filter.mpr
      exact ⟨by simp, by
        apply decide_eq_true
        exact ⟨e,he,of_decide_eq_true hl,rfl⟩⟩)
  rw [hl,hrn] at hm
  exact Nat.le_of_mul_le_mul_left hm hb

/-- Every edge remains its original identity after deletion. -/
def Bipartite.remove {L R : Nat} (G : Bipartite L R) (selected : G.Edge → Bool) : Bipartite L R where
  Edge := G.Edge
  edges := G.edges.filter (fun e => !selected e)
  distinct := G.distinct.filter _
  left := G.left
  right := G.right

/-- An actual selected indexed-edge subset with one incident edge per vertex. -/
def Bipartite.PerfectMatching {L R : Nat} (G : Bipartite L R) (selected : G.Edge → Bool) : Prop :=
  (∀ x, (G.edges.filter selected).countP (fun e => decide (G.left e = x)) = 1) ∧
  (∀ y, (G.edges.filter selected).countP (fun e => decide (G.right e = y)) = 1)

theorem countP_split {E : Type} (es : List E) (p selected : E → Bool) :
    (es.filter selected).countP p + (es.filter (fun e => !selected e)).countP p = es.countP p := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hs : selected e <;> cases hp : p e <;>
      simp_all <;> omega

/-- Removing one actual perfect matching lowers every degree by exactly one. -/
theorem Bipartite.remove_regular {L R : Nat} (G : Bipartite L R) (b : Nat)
    (hr : G.Regular (b+1)) (selected : G.Edge → Bool) (hm : G.PerfectMatching selected) :
    (G.remove selected).Regular b := by
  constructor
  · intro x
    have hs := countP_split G.edges (fun e => decide (G.left e = x)) selected
    rw [hm.1 x,hr.1 x] at hs
    change (G.edges.filter (fun e => !selected e)).countP (fun e => decide (G.left e = x)) = b
    omega
  · intro y
    have hs := countP_split G.edges (fun e => decide (G.right e = y)) selected
    rw [hm.2 y,hr.2 y] at hs
    change (G.edges.filter (fun e => !selected e)).countP (fun e => decide (G.right e = y)) = b
    omega

/-- Degree one supplies a perfect matching constructively: select all edge identities. -/
theorem Bipartite.degree_one_matching {L R : Nat} (G : Bipartite L R)
    (hr : G.Regular 1) : G.PerfectMatching (fun _ => true) := by
  have hf : G.edges.filter (fun _ => true) = G.edges := by
    induction G.edges <;> simp_all
  simpa [PerfectMatching, Regular, hf] using hr

/-- Edge labels must count each original indexed edge and each vertex incidence. -/
def Bipartite.EdgeColoring {L R : Nat} (G : Bipartite L R) (b : Nat)
    (color : G.Edge → Fin b) : Prop :=
  (∀ x c, G.edges.countP (fun e => decide (G.left e = x ∧ color e = c)) = 1) ∧
  (∀ y c, G.edges.countP (fun e => decide (G.right e = y ∧ color e = c)) = 1)

theorem Bipartite.degree_one_coloring {L R : Nat} (G : Bipartite L R)
    (hr : G.Regular 1) : G.EdgeColoring 1 (fun _ => 0) := by
  constructor
  · intro x c
    have hc : c = 0 := by apply Fin.ext; have := c.isLt; simp only [Fin.val_zero]; omega
    simpa [hc] using hr.1 x
  · intro y c
    have hc : c = 0 := by apply Fin.ext; have := c.isLt; simp only [Fin.val_zero]; omega
    simpa [hc] using hr.2 y

/-- Natural labels with a proved bound only on actual edges permit the empty
zero-color case even when the ambient edge type retains removed identities. -/
def Bipartite.Labeling {L R : Nat} (G : Bipartite L R) (b : Nat)
    (color : G.Edge → Nat) : Prop :=
  (∀ e ∈ G.edges, color e < b) ∧
  (∀ x (c : Fin b), G.edges.countP (fun e => decide (G.left e = x ∧ color e = c.val)) = 1) ∧
  (∀ y (c : Fin b), G.edges.countP (fun e => decide (G.right e = y ∧ color e = c.val)) = 1)

def liftColor {E : Type} (selected : E → Bool) (color : E → Nat) (e : E) : Nat :=
  if selected e then 0 else color e + 1

theorem lift_zero_count {E V : Type} [DecidableEq V] (es : List E) (f : E → V)
    (v : V) (selected : E → Bool) (color : E → Nat) :
    es.countP (fun e => decide (f e = v ∧ liftColor selected color e = 0)) =
      (es.filter selected).countP (fun e => decide (f e = v)) := by
  rw [List.countP_filter]
  congr 1
  funext e
  cases hs : selected e <;> simp [liftColor, hs]

theorem lift_succ_count {E V : Type} [DecidableEq V] (es : List E) (f : E → V)
    (v : V) (selected : E → Bool) (color : E → Nat) (c : Nat) :
    es.countP (fun e => decide (f e = v ∧ liftColor selected color e = c+1)) =
      (es.filter (fun e => !selected e)).countP (fun e => decide (f e = v ∧ color e = c)) := by
  rw [List.countP_filter]
  congr 1
  funext e
  cases hs : selected e <;> simp [liftColor, hs]

/-- Concrete inductive coloring step: label one supplied matching zero and
shift every actual residual edge label by one. No existence is postulated. -/
theorem Bipartite.lift_labeling {L R : Nat} (G : Bipartite L R) (b : Nat)
    (selected : G.Edge → Bool) (hm : G.PerfectMatching selected) (color : G.Edge → Nat)
    (hc : (G.remove selected).Labeling b color) :
    G.Labeling (b+1) (liftColor selected color) := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    cases hs : selected e
    · have hre : e ∈ (G.remove selected).edges := List.mem_filter.mpr ⟨he,by simp [hs]⟩
      have hbound := hc.1 e hre
      simp only [liftColor, hs, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp [liftColor, hs]
  · intro x c
    cases hv : c.val with
    | zero => simpa [hv] using (lift_zero_count G.edges G.left x selected color).trans (hm.1 x)
    | succ d =>
      have hd : d < b := by have := c.isLt; omega
      have ht := hc.2.1 x ⟨d,hd⟩
      simpa [hv] using (lift_succ_count G.edges G.left x selected color d).trans ht
  · intro y c
    cases hv : c.val with
    | zero => simpa [hv] using (lift_zero_count G.edges G.right y selected color).trans (hm.2 y)
    | succ d =>
      have hd : d < b := by have := c.isLt; omega
      have ht := hc.2.2 y ⟨d,hd⟩
      simpa [hv] using (lift_succ_count G.edges G.right y selected color d).trans ht

theorem Bipartite.zero_regular_empty {L R : Nat} (G : Bipartite L R)
    (hr : G.Regular 0) : G.edges = [] := by
  cases he : G.edges with
  | nil => rfl
  | cons e es =>
    have hc := hr.1 (G.left e)
    rw [he,List.countP_cons] at hc
    simp at hc

theorem Bipartite.zero_labeling {L R : Nat} (G : Bipartite L R)
    (hr : G.Regular 0) : G.Labeling 0 (fun _ => 0) := by
  have he := G.zero_regular_empty hr
  refine ⟨?_,?_,?_⟩
  · intro e hm; simp [he] at hm
  · intro x c; exact Fin.elim0 c
  · intro y c; exact Fin.elim0 c

/-- Positive regularity forces equal bipartition sizes; this is derived from
actual edge counts and does not impose simplicity on the graph. -/
theorem Bipartite.equal_sides {L R : Nat} (G : Bipartite L R) (b : Nat)
    (hb : 0 < b) (hr : G.Regular b) : L = R := by
  have hl := G.subset_degree b hr (List.finRange L) (List.nodup_finRange L)
  have hcl : G.edges.countP (fun e => decide (G.left e ∈ List.finRange L)) = G.edges.length :=
    List.countP_eq_length.mpr (by intro e _; simp)
  have hrr : G.edges.countP (fun e => decide (G.right e ∈ List.finRange R)) = b*R := by
    rw [←fiber_sum G.edges G.right (List.finRange R) (List.nodup_finRange R)]
    simpa using constant_sum (List.finRange R) _ b (fun y _ => hr.2 y)
  have hcr : G.edges.countP (fun e => decide (G.right e ∈ List.finRange R)) = G.edges.length :=
    List.countP_eq_length.mpr (by intro e _; simp)
  simp only [List.length_finRange] at hl
  rw [hcl] at hl
  rw [hcr] at hrr
  exact Nat.le_antisymm
    (Nat.le_of_mul_le_mul_left (by omega : b*L ≤ b*R) hb)
    (Nat.le_of_mul_le_mul_left (by omega : b*R ≤ b*L) hb)

/-- Delete a chosen left/right vertex pair, retaining all other original edge identities. -/
def Bipartite.deleteVertices {L R : Nat} (G : Bipartite L R) (x : Fin L) (y : Fin R) : Bipartite L R where
  Edge := G.Edge
  edges := G.edges.filter (fun e => decide (G.left e ≠ x ∧ G.right e ≠ y))
  distinct := G.distinct.filter _
  left := G.left
  right := G.right

theorem Bipartite.delete_neighbors {L R : Nat} (G : Bipartite L R)
    (x : Fin L) (y : Fin R) (A : List (Fin L)) (hx : x ∉ A) :
    (G.deleteVertices x y).neighbors A = (G.neighbors A).filter (fun z => decide (z ≠ y)) := by
  simp only [neighbors, List.filter_filter]
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  change (∃ e ∈ G.edges.filter (fun e => decide (G.left e ≠ x ∧ G.right e ≠ y)),
    G.left e ∈ A ∧ G.right e = z) ↔
    z ≠ y ∧ (∃ e ∈ G.edges, G.left e ∈ A ∧ G.right e = z)
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e,⟨he,hed⟩,hea,hez⟩
    exact ⟨hez ▸ hed.2,⟨e,he,hea,hez⟩⟩
  · rintro ⟨hzy,⟨e,he,hea,hez⟩⟩
    refine ⟨e,⟨he,?_,?_⟩,hea,hez⟩
    · intro hex; exact hx (hex ▸ hea)
    · exact fun hey => hzy (hez.symm.trans hey)

theorem filter_ne_length {V : Type} [DecidableEq V] (xs : List V) (y : V)
    (hn : xs.Nodup) :
    (xs.filter (fun z => decide (z ≠ y))).length + (if y ∈ xs then 1 else 0) = xs.length := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
    obtain ⟨hz,hnz⟩ := List.nodup_cons.mp hn
    have hi := ih hnz
    by_cases hzy : z = y
    · subst z
      have hy : y ∉ zs := hz
      simp [hy] at hi ⊢
      exact hi
    · have hyz : y ≠ z := Ne.symm hzy
      by_cases hy : y ∈ zs <;> simp [hzy,hyz,hy] at hi ⊢ <;> omega

/-- The strict branch of Hall's induction survives deletion of an arbitrary
chosen pair. Only subsets of the remaining left vertices are quantified. -/
theorem Bipartite.strict_delete_hall {L R : Nat} (G : Bipartite L R)
    (x : Fin L) (y : Fin R)
    (hs : ∀ A : List (Fin L), A.Nodup → x ∉ A → A ≠ [] →
      A.length < (G.neighbors A).length)
    (A : List (Fin L)) (ha : A.Nodup) (hx : x ∉ A) :
    A.length ≤ ((G.deleteVertices x y).neighbors A).length := by
  by_cases he : A = []
  · subst A; simp
  · have hi := hs A ha hx he
    have hf := filter_ne_length (G.neighbors A) y (G.neighbors_distinct A)
    rw [G.delete_neighbors x y A hx]
    split at hf <;> omega

def Bipartite.deleteSubset {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) : Bipartite L R where
  Edge := G.Edge
  edges := G.edges.filter (fun e => decide (G.left e ∉ A ∧ G.right e ∉ G.neighbors A))
  distinct := G.distinct.filter _
  left := G.left
  right := G.right

theorem Bipartite.mem_neighbors {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) (y : Fin R) :
    y ∈ G.neighbors A ↔ ∃ e ∈ G.edges, G.left e ∈ A ∧ G.right e = y := by
  simp [neighbors]

theorem Bipartite.deleteSubset_neighbors {L R : Nat} (G : Bipartite L R)
    (A B : List (Fin L)) (hd : ∀ x ∈ B, x ∉ A) :
    (G.deleteSubset A).neighbors B = (G.neighbors B).filter (fun z => decide (z ∉ G.neighbors A)) := by
  simp only [neighbors, List.filter_filter]
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  simp only [deleteSubset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨e,he,heb,hez⟩
    have hem := List.mem_filter.mp he
    have hed : G.left e ∉ A ∧ G.right e ∉ G.neighbors A := of_decide_eq_true hem.2
    refine ⟨?_,⟨e,hem.1,heb,hez⟩⟩
    have hz : z ∉ G.neighbors A := hez ▸ hed.2
    simpa only [neighbors, List.mem_filter, decide_eq_true_eq] using hz
  · rintro ⟨hz,⟨e,he,heb,hez⟩⟩
    refine ⟨e,List.mem_filter.mpr ⟨he,?_⟩,heb,hez⟩
    apply decide_eq_true
    have hzn : z ∉ G.neighbors A := by
      simpa only [neighbors, List.mem_filter, decide_eq_true_eq] using hz
    exact ⟨hd _ heb,hez.symm ▸ hzn⟩

theorem filter_union_length {V : Type} (xs : List V) (p q : V → Bool) :
    (xs.filter (fun x => p x || q x)).length =
      (xs.filter p).length + (xs.filter (fun x => q x && !p x)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

theorem Bipartite.union_neighbors_length {L R : Nat} (G : Bipartite L R)
    (A B : List (Fin L)) :
    (G.neighbors (A++B)).length = (G.neighbors A).length +
      ((G.neighbors B).filter (fun z => decide (z ∉ G.neighbors A))).length := by
  let p := fun z => decide (∃ e ∈ G.edges, G.left e ∈ A ∧ G.right e = z)
  let q := fun z => decide (∃ e ∈ G.edges, G.left e ∈ B ∧ G.right e = z)
  have hu : (fun z => decide (∃ e ∈ G.edges, G.left e ∈ A++B ∧ G.right e = z)) =
      (fun z => p z || q z) := by
    funext z; apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, p, q]
    constructor
    · rintro ⟨e,he,hab,hez⟩
      rcases List.mem_append.mp hab with ha | hb
      · exact Or.inl ⟨e,he,ha,hez⟩
      · exact Or.inr ⟨e,he,hb,hez⟩
    · rintro (⟨e,he,ha,hez⟩ | ⟨e,he,hb,hez⟩)
      · exact ⟨e,he,List.mem_append.mpr (Or.inl ha),hez⟩
      · exact ⟨e,he,List.mem_append.mpr (Or.inr hb),hez⟩
  have hn : (fun z => decide (z ∉ G.neighbors A)) = (fun z => !p z) := by
    funext z; apply Bool.eq_iff_iff.mpr
    simp [G.mem_neighbors, p]
  rw [hn]
  simp only [neighbors, List.filter_filter, hu]
  simpa only [Bool.and_comm] using filter_union_length (List.finRange R) p q

/-- The tight-subset branch of Hall's induction: the complement retains Hall
because the tight neighborhood exhausts exactly its available cardinality. -/
theorem Bipartite.tight_delete_hall {L R : Nat} (G : Bipartite L R)
    (hall : ∀ C : List (Fin L), C.Nodup → C.length ≤ (G.neighbors C).length)
    (A B : List (Fin L)) (ha : A.Nodup) (hb : B.Nodup)
    (hd : ∀ x ∈ B, x ∉ A) (ht : A.length = (G.neighbors A).length) :
    B.length ≤ ((G.deleteSubset A).neighbors B).length := by
  have hab : (A++B).Nodup := List.nodup_append.mpr ⟨ha,hb,by
    intro x hx y hy he
    subst y
    exact hd x hy hx⟩
  have hc := hall (A++B) hab
  rw [List.length_append,G.union_neighbors_length A B] at hc
  rw [G.deleteSubset_neighbors A B hd]
  omega

/-- Tight-side subgraph; right endpoints already lie in its actual neighborhood. -/
def Bipartite.restrictLeft {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) : Bipartite L R where
  Edge := G.Edge
  edges := G.edges.filter (fun e => decide (G.left e ∈ A))
  distinct := G.distinct.filter _
  left := G.left
  right := G.right

theorem Bipartite.restrictLeft_neighbors {L R : Nat} (G : Bipartite L R)
    (A B : List (Fin L)) (hs : ∀ x ∈ B, x ∈ A) :
    (G.restrictLeft A).neighbors B = G.neighbors B := by
  simp only [neighbors]
  congr 1
  funext z
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change (∃ e ∈ G.edges.filter (fun e => decide (G.left e ∈ A)),
      G.left e ∈ B ∧ G.right e = z) ↔
    (∃ e ∈ G.edges, G.left e ∈ B ∧ G.right e = z)
  constructor
  · rintro ⟨e,he,heb,hez⟩
    exact ⟨e,(List.mem_filter.mp he).1,heb,hez⟩
  · rintro ⟨e,he,heb,hez⟩
    exact ⟨e,List.mem_filter.mpr ⟨he,by simpa using hs _ heb⟩,heb,hez⟩

#print axioms Bipartite.hall
#print axioms Bipartite.tight_delete_hall
#print axioms Bipartite.strict_delete_hall
#print axioms Bipartite.remove_regular
#print axioms Bipartite.lift_labeling
#print axioms Bipartite.degree_one_coloring
end ErdePaths.HallColor
