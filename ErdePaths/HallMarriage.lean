import ErdePaths.HallColor

namespace ErdePaths.HallMarriage
open HallColor

/-- Actual indexed edges match every active left vertex, with distinct right
endpoints. Dependence on membership proofs is harmless by proof irrelevance. -/
structure Matching {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) where
  edge : ∀ x, x ∈ A → G.Edge
  valid : ∀ x h, edge x h ∈ G.edges
  left_eq : ∀ x h, G.left (edge x h) = x
  right_injective : ∀ x y hx hy,
    G.right (edge x hx) = G.right (edge y hy) → x = y

def ActiveHall {L R : Nat} (G : Bipartite L R) (A : List (Fin L)) : Prop :=
  ∀ B : List (Fin L), B.Nodup → (∀ x ∈ B, x ∈ A) → B.length ≤ (G.neighbors B).length

noncomputable def emptyMatching {L R : Nat} (G : Bipartite L R) : Matching G [] where
  edge := fun x h => False.elim (by simp at h)
  valid := fun x h => False.elim (by simp at h)
  left_eq := fun x h => False.elim (by simp at h)
  right_injective := fun x y hx _ _ => False.elim (by simp at hx)

/-- Add the actual edge xy after matching the remaining vertices in the graph
that deleted x and y. No new matching existence is assumed. -/
noncomputable def extend {L R : Nat} (G : Bipartite L R) (x : Fin L) (xs : List (Fin L))
    (_hx : x ∉ xs) (e : G.Edge) (he : e ∈ G.edges) (hel : G.left e = x)
    (M : Matching (G.deleteVertices x (G.right e)) xs) : Matching G (x::xs) := by
  let f : ∀ z, z ∈ x::xs → G.Edge := fun z hz =>
    if hzx : z = x then e else M.edge z ((List.mem_cons.mp hz).resolve_left hzx)
  refine ⟨f,?_,?_,?_⟩
  · intro z hz
    by_cases hzx : z = x <;> simp only [f,hzx,↓reduceDIte]
    · exact he
    · exact (List.mem_filter.mp (M.valid z _)).1
  · intro z hz
    by_cases hzx : z = x <;> simp only [f,hzx,↓reduceDIte]
    · exact hel
    · exact M.left_eq z _
  · intro z w hz hw hr
    by_cases hzx : z = x <;> by_cases hwx : w = x
    · exact hzx.trans hwx.symm
    · have hwm := (List.mem_filter.mp (M.valid w ((List.mem_cons.mp hw).resolve_left hwx))).2
      have hwr : G.right (M.edge w _) ≠ G.right e := (of_decide_eq_true hwm).2
      simp only [f,hzx,hwx,↓reduceDIte] at hr
      exact False.elim (hwr hr.symm)
    · have hzm := (List.mem_filter.mp (M.valid z ((List.mem_cons.mp hz).resolve_left hzx))).2
      have hzr : G.right (M.edge z _) ≠ G.right e := (of_decide_eq_true hzm).2
      simp only [f,hzx,hwx,↓reduceDIte] at hr
      exact False.elim (hzr hr)
    · simp only [f,hzx,hwx,↓reduceDIte] at hr
      exact M.right_injective z w _ _ hr

/-- Glue actual matchings of a tight-side subgraph and its deleted complement.
Their right endpoints lie respectively inside and outside N(C). -/
noncomputable def glue {L R : Nat} (G : Bipartite L R) (A C : List (Fin L))
    (_hc : ∀ x ∈ C, x ∈ A)
    (M : Matching (G.restrictLeft C) C)
    (N : Matching (G.deleteSubset C) (A.filter (fun x => decide (x ∉ C)))) : Matching G A := by
  let f : ∀ x, x ∈ A → G.Edge := fun x hx =>
    if hxc : x ∈ C then M.edge x hxc else N.edge x (List.mem_filter.mpr ⟨hx,by simpa using hxc⟩)
  refine ⟨f,?_,?_,?_⟩
  · intro x hx
    by_cases hxc : x ∈ C <;> simp only [f,hxc,↓reduceDIte]
    · exact (List.mem_filter.mp (M.valid x _)).1
    · exact (List.mem_filter.mp (N.valid x _)).1
  · intro x hx
    by_cases hxc : x ∈ C <;> simp only [f,hxc,↓reduceDIte]
    · exact M.left_eq x _
    · exact N.left_eq x _
  · intro x y hx hy hr
    have mr (z : Fin L) (hz : z ∈ C) : G.right (M.edge z hz) ∈ G.neighbors C := by
      apply (G.mem_neighbors C _).mpr
      exact ⟨M.edge z hz,(List.mem_filter.mp (M.valid z hz)).1,
        (M.left_eq z hz).symm ▸ hz,rfl⟩
    have nr (z : Fin L) (hz : z ∈ A.filter (fun x => decide (x ∉ C))) :
        G.right (N.edge z hz) ∉ G.neighbors C :=
      (of_decide_eq_true (List.mem_filter.mp (N.valid z hz)).2).2
    by_cases hxc : x ∈ C <;> by_cases hyc : y ∈ C
    · simp only [f,hxc,hyc,↓reduceDIte] at hr
      exact M.right_injective x y _ _ hr
    · simp only [f,hxc,hyc,↓reduceDIte] at hr
      exact False.elim (nr y _ (hr ▸ mr x hxc))
    · simp only [f,hxc,hyc,↓reduceDIte] at hr
      exact False.elim (nr x _ (hr.symm ▸ mr y hyc))
    · simp only [f,hxc,hyc,↓reduceDIte] at hr
      exact N.right_injective x y _ _ hr

theorem filter_length_lt {V : Type} (xs : List V) (p : V → Bool)
    (h : ∃ x ∈ xs, p x = false) : (xs.filter p).length < xs.length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases hp : p x
    · have hl := List.length_filter_le p xs
      simp [hp]; omega
    · obtain ⟨y,hy,hpy⟩ := h
      have hym : y ∈ xs := by
        rcases List.mem_cons.mp hy with he | he
        · subst y; simp [hp] at hpy
        · exact he
      have hi := ih ⟨y,hym,hpy⟩
      simpa only [List.filter_cons,hp,↓reduceIte,List.length_cons] using Nat.succ_lt_succ hi

/-- Uniform finite Hall marriage theorem with active vertex lists. -/
theorem exists_matching {L R : Nat} (G : Bipartite L R) (A : List (Fin L))
    (ha : A.Nodup) (hall : ActiveHall G A) : Nonempty (Matching G A) := by
  classical
  by_cases ht : ∃ C : List (Fin L), C.Nodup ∧ (∀ x ∈ C, x ∈ A) ∧
      0 < C.length ∧ C.length < A.length ∧ C.length = (G.neighbors C).length
  · obtain ⟨C,hcn,hca,hcp,hcl,hct⟩ := ht
    let D := A.filter (fun x => decide (x ∉ C))
    have hdn : D.Nodup := ha.filter _
    have hds (x : Fin L) (hx : x ∈ D) : x ∈ A ∧ x ∉ C := by
      have hm := List.mem_filter.mp hx
      exact ⟨hm.1,of_decide_eq_true hm.2⟩
    have hdl : D.length < A.length := by
      cases hc : C with
      | nil => simp [hc] at hcp
      | cons c cs =>
        apply filter_length_lt
        refine ⟨c,hca c (by simp [hc]),?_⟩
        simp [hc]
    have hch : ActiveHall (G.restrictLeft C) C := by
      intro B hbn hbc
      rw [G.restrictLeft_neighbors C B hbc]
      exact hall B hbn (fun x hx => hca x (hbc x hx))
    have hdh : ActiveHall (G.deleteSubset C) D := by
      intro B hbn hbd
      have hd (x : Fin L) (hx : x ∈ B) : x ∉ C := (hds x (hbd x hx)).2
      have hcb : (C++B).Nodup := List.nodup_append.mpr ⟨hcn,hbn,by
        intro x hx y hy he; subst y; exact hd x hy hx⟩
      have hi := hall (C++B) hcb (by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hca x hx
        · exact (hds x (hbd x hx)).1)
      rw [List.length_append,G.union_neighbors_length C B] at hi
      rw [G.deleteSubset_neighbors C B hd]
      omega
    obtain ⟨M⟩ := exists_matching (G.restrictLeft C) C hcn hch
    obtain ⟨N⟩ := exists_matching (G.deleteSubset C) D hdn hdh
    exact ⟨glue G A C hca M N⟩
  · cases A with
    | nil => exact ⟨emptyMatching G⟩
    | cons x xs =>
      obtain ⟨hx,hxs⟩ := List.nodup_cons.mp ha
      have hn : 0 < (G.neighbors [x]).length := by
        have hi := hall [x] (by simp) (by intro z hz; simp at hz; subst z; simp)
        simp only [List.length_cons,List.length_nil] at hi
        omega
      obtain ⟨y,hy⟩ : ∃ y, y ∈ G.neighbors [x] := by
        cases hc : G.neighbors [x] with
        | nil => simp [hc] at hn
        | cons y ys => exact ⟨y,by simp⟩
      obtain ⟨e,he,hel,her⟩ := (G.mem_neighbors [x] y).mp hy
      have hel' : G.left e = x := by simpa using hel
      have hsh : ActiveHall (G.deleteVertices x y) xs := by
        intro B hbn hbs
        have hbx : x ∉ B := fun he => hx (hbs x he)
        by_cases hbe : B = []
        · subst B; simp
        · have hbpos := List.ne_nil_iff_length_pos.mp hbe
          have hbl := hbn.length_le_of_subset hbs
          have hi := hall B hbn (fun z hz => List.mem_cons.mpr (Or.inr (hbs z hz)))
          have hneq : B.length ≠ (G.neighbors B).length := by
            intro heq
            exact ht ⟨B,hbn,(fun z hz => List.mem_cons.mpr (Or.inr (hbs z hz))),
              hbpos,by simp only [List.length_cons]; omega,heq⟩
          have hstrict : B.length < (G.neighbors B).length := by omega
          have hf := HallColor.filter_ne_length (G.neighbors B) y (G.neighbors_distinct B)
          rw [G.delete_neighbors x y B hbx]
          split at hf <;> omega
      obtain ⟨M⟩ := exists_matching (G.deleteVertices x y) xs hxs hsh
      have MM : Matching (G.deleteVertices x (G.right e)) xs := by simpa [her] using M
      exact ⟨extend G x xs hx e he hel' MM⟩
termination_by A.length
decreasing_by
  all_goals first | exact hcl | exact hdl | (simp_all only [List.length_cons]; omega)

theorem nodup_count_one {V : Type} [DecidableEq V] (xs : List V) (hn : xs.Nodup)
    (v : V) (hv : v ∈ xs) : xs.countP (fun x => decide (x = v)) = 1 := by
  have hc := hn.count (a := v)
  simp only [List.count_eq_countP,hv,ite_true] at hc
  have hp : (fun x : V => decide (x = v)) = (fun x => x == v) := by
    funext x; apply Bool.eq_iff_iff.mpr; simp
  rw [hp]; exact hc

/-- A full left matching in an equal-size bipartition also saturates the right. -/
theorem full_right_surjective {L R : Nat} (G : Bipartite L R) (heq : L = R)
    (M : Matching G (List.finRange L)) (y : Fin R) :
    ∃ x : Fin L, G.right (M.edge x (List.mem_finRange x)) = y := by
  classical
  let f := fun x : Fin L => G.right (M.edge x (List.mem_finRange x))
  have hn : ((List.finRange L).map f).Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (S := fun x z => f x ≠ f z)
      (fun h he => h (M.right_injective _ _ _ _ he)) (List.nodup_finRange L)
  apply Classical.byContradiction
  intro h
  have hy : ∀ x, f x ≠ y := by simpa [f] using h
  have hs : (List.finRange L).map f ⊆ (List.finRange R).filter (fun z => decide (z ≠ y)) := by
    intro z hz
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact List.mem_filter.mpr ⟨by simp,by simpa using hy x⟩
  have hl := hn.length_le_of_subset hs
  have hf := HallColor.filter_ne_length (List.finRange R) y (List.nodup_finRange R)
  simp only [List.length_map,List.length_finRange] at hl
  simp only [List.mem_finRange,ite_true,List.length_finRange] at hf
  omega

/-- Unconditional perfect matching existence for every positive regular finite
bipartite multigraph, retaining exact original edge identities. -/
theorem regular_perfect_matching {L R : Nat} (G : Bipartite L R) (b : Nat)
    (hb : 0 < b) (hr : G.Regular b) :
    ∃ selected : G.Edge → Bool, G.PerfectMatching selected := by
  classical
  have hh : ActiveHall G (List.finRange L) := by
    intro A ha _; exact G.hall b hb hr A ha
  obtain ⟨M⟩ := exists_matching G (List.finRange L) (List.nodup_finRange L) hh
  let f := fun x : Fin L => M.edge x (List.mem_finRange x)
  let chosen := (List.finRange L).map f
  have hln : (chosen.map G.left).Nodup := by
    have he : chosen.map G.left = List.finRange L := by
      simp only [chosen,List.map_map]
      have hf : G.left ∘ f = id := by funext x; exact M.left_eq x _
      rw [hf]; simp
    rw [he]; exact List.nodup_finRange L
  have hcn : chosen.Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (S := fun x z => f x ≠ f z)
      (fun h he => h (by have hh := congrArg G.left he; simpa [f,M.left_eq] using hh))
      (List.nodup_finRange L)
  have hrn : (chosen.map G.right).Nodup := by
    simp only [chosen,List.map_map]
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (S := fun x z => G.right (f x) ≠ G.right (f z))
      (fun h he => h (M.right_injective _ _ _ _ he)) (List.nodup_finRange L)
  let selected := fun e => decide (e ∈ chosen)
  have hperm : (G.edges.filter selected).Perm chosen := by
    apply (List.perm_ext_iff_of_nodup (G.distinct.filter _) hcn).mpr
    intro e
    constructor
    · intro he; exact of_decide_eq_true (List.mem_filter.mp he).2
    · intro he
      obtain ⟨x,_,hx⟩ := List.mem_map.mp he
      exact List.mem_filter.mpr ⟨hx ▸ M.valid x _,by simpa [selected] using he⟩
  refine ⟨selected,?_,?_⟩
  · intro x
    have hx : x ∈ chosen.map G.left := by
      apply List.mem_map.mpr
      exact ⟨f x,List.mem_map.mpr ⟨x,by simp,rfl⟩,M.left_eq x _⟩
    have hc := nodup_count_one _ hln x hx
    rw [List.countP_map] at hc
    exact (hperm.countP_eq _).trans hc
  · intro y
    obtain ⟨x,hxy⟩ := full_right_surjective G (G.equal_sides b hb hr) M y
    have hy : y ∈ chosen.map G.right :=
      List.mem_map.mpr ⟨f x,List.mem_map.mpr ⟨x,by simp,rfl⟩,hxy⟩
    have hc := nodup_count_one _ hrn y hy
    rw [List.countP_map] at hc
    exact (hperm.countP_eq _).trans hc

/-- Every finite regular bipartite multigraph has exactly b labels, each
occurring once at every vertex. Parallel edges keep their original identities. -/
theorem regular_labeling {L R : Nat} (b : Nat) (G : Bipartite L R) (hr : G.Regular b) :
    ∃ color : G.Edge → Nat, G.Labeling b color := by
  induction b generalizing G with
  | zero => exact ⟨fun _ => 0,G.zero_labeling hr⟩
  | succ b ih =>
    obtain ⟨selected,hm⟩ := regular_perfect_matching G (b+1) (by omega) hr
    have hrr := G.remove_regular b hr selected hm
    obtain ⟨color,hc⟩ := ih (G.remove selected) hrr
    exact ⟨liftColor selected color,G.lift_labeling b selected hm color hc⟩

#print axioms regular_labeling
#print axioms regular_perfect_matching
#print axioms exists_matching
#print axioms extend
#print axioms glue
end ErdePaths.HallMarriage
