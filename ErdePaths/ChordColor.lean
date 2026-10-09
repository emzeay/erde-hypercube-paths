import ErdePaths.ChordGraph
import ErdePaths.HallMarriage

namespace ErdePaths.ChordColor
open ChordGraph HallColor

structure Enumeration (V : Type) where
  vertices : List V
  distinct : vertices.Nodup
  covers : ∀ v, v ∈ vertices

abbrev side {V : Type} (E : Enumeration V) (χ : V → Bool) (c : Bool) : List V :=
  E.vertices.filter (fun v => χ v == c)

def endpoint {V : Type} (χ : V → Bool) (c : Bool) (p : V × V) : V :=
  if χ p.1 = c then p.1 else p.2

theorem endpoint_color {V : Type} (χ : V → Bool) (c : Bool) (p : V × V)
    (hp : χ p.1 ≠ χ p.2) : χ (endpoint χ c p) = c := by
  cases h1 : χ p.1 <;> cases h2 : χ p.2 <;> cases c <;> simp_all [endpoint]

theorem endpoint_eq_iff {V : Type} (χ : V → Bool) (c : Bool) (p : V × V)
    (hp : χ p.1 ≠ χ p.2) (v : V) (hv : χ v = c) :
    endpoint χ c p = v ↔ p.1 = v ∨ p.2 = v := by
  by_cases h1 : χ p.1 = c
  · have hn : p.2 ≠ v := fun he => hp (h1.trans ((congrArg χ he).trans hv).symm)
    simp [endpoint,h1,hn]
  · have hn : p.1 ≠ v := fun he => h1 ((congrArg χ he).trans hv)
    simp [endpoint,h1,hn]

def code {V : Type} [DecidableEq V] (xs : List V) (v : V) (hv : v ∈ xs) : Fin xs.length :=
  ⟨xs.idxOf v,List.idxOf_lt_length_iff.mpr hv⟩

theorem decode_code {V : Type} [DecidableEq V] (xs : List V) (v : V) (hv : v ∈ xs) :
    xs[code xs v hv] = v := List.getElem_idxOf _

theorem code_eq_iff {V : Type} [DecidableEq V] (xs : List V) (hn : xs.Nodup)
    (v : V) (hv : v ∈ xs) (i : Fin xs.length) : code xs v hv = i ↔ v = xs[i] := by
  constructor
  · intro he; simpa [he] using (decode_code xs v hv).symm
  · intro he
    apply Fin.ext
    subst v
    exact hn.idxOf_getElem i.val i.isLt

def original {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (G : RegularChordGraph V χ b) (i : Fin G.edges.length) : G.Edge := G.edges[i]

def physical {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (G : RegularChordGraph V χ b) (c : Bool) (i : Fin G.edges.length) : V :=
  endpoint χ c (G.ends (original G i))

theorem physical_color {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (G : RegularChordGraph V χ b) (c : Bool) (i : Fin G.edges.length) :
    χ (physical G c i) = c :=
  endpoint_color χ c _ (G.opposite _ (List.getElem_mem i.isLt))

def vertexCode {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (E : Enumeration V) (G : RegularChordGraph V χ b) (c : Bool) (i : Fin G.edges.length) :
    Fin (side E χ c).length := code (side E χ c) (physical G c i)
      (List.mem_filter.mpr ⟨E.covers _,by simp [physical_color G c i]⟩)

def graph {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (E : Enumeration V) (G : RegularChordGraph V χ b) :
    Bipartite (side E χ false).length (side E χ true).length where
  Edge := Fin G.edges.length
  edges := List.finRange G.edges.length
  distinct := List.nodup_finRange _
  left := vertexCode E G false
  right := vertexCode E G true

theorem vertexCode_incident {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (E : Enumeration V) (G : RegularChordGraph V χ b) (c : Bool)
    (i : Fin G.edges.length) (v : Fin (side E χ c).length) :
    vertexCode E G c i = v ↔ (G.ends (original G i)).1 = (side E χ c)[v] ∨
      (G.ends (original G i)).2 = (side E χ c)[v] := by
  rw [vertexCode,code_eq_iff _ (E.distinct.filter _)]
  apply endpoint_eq_iff χ c _ (G.opposite _ (List.getElem_mem i.isLt))
  have hm := (List.mem_filter.mp (List.getElem_mem (l := side E χ c) v.isLt)).2
  simpa using hm

theorem graph_regular {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (E : Enumeration V) (G : RegularChordGraph V χ b) : (graph E G).Regular b := by
  have hg : (List.finRange G.edges.length).map (original G) = G.edges := by
    simp [original,List.finRange,List.map_ofFn,Function.comp_def]
  have hc (c : Bool) (v : Fin (side E χ c).length) :
      (List.finRange G.edges.length).countP (fun i => decide (vertexCode E G c i = v)) = b := by
    have hr := G.regular (side E χ c)[v]
    rw [←hg,List.countP_map] at hr
    have hp : (fun i => decide (vertexCode E G c i = v)) =
        ((fun e => decide ((G.ends e).1 = (side E χ c)[v] ∨ (G.ends e).2 = (side E χ c)[v])) ∘ original G) := by
      funext i; apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,Function.comp_apply]
      exact vertexCode_incident E G c i v
    rw [hp]; exact hr
  exact ⟨hc false,hc true⟩

def PhysicalColoring {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (G : RegularChordGraph V χ b) (color : G.Edge → Nat) : Prop :=
  (∀ e ∈ G.edges, color e < b) ∧
  (∀ v (c : Fin b), G.edges.countP (fun e => decide
    (((G.ends e).1 = v ∨ (G.ends e).2 = v) ∧ color e = c.val)) = 1)

/-- Coloring the actual physical chord graph is an unconditional application
of proved Hall marriage, not a supplied coloring hypothesis. -/
theorem exists_physical_coloring {V : Type} [DecidableEq V] {χ : V → Bool} {b : Nat}
    (E : Enumeration V) (G : RegularChordGraph V χ b) :
    ∃ color : G.Edge → Nat, PhysicalColoring G color := by
  classical
  obtain ⟨col,hcol⟩ := HallMarriage.regular_labeling b (graph E G) (graph_regular E G)
  have hi (v : V) (c : Fin b) : (List.finRange G.edges.length).countP
      (fun i => decide (((G.ends (original G i)).1 = v ∨ (G.ends (original G i)).2 = v) ∧ col i = c.val)) = 1 := by
    let s := χ v
    have hvm : v ∈ side E χ s := List.mem_filter.mpr ⟨E.covers v,by simp [s]⟩
    let j := code (side E χ s) v hvm
    have hj : (side E χ s)[j] = v := decode_code _ _ _
    have hc : (List.finRange G.edges.length).countP
        (fun i => decide (vertexCode E G s i = j ∧ col i = c.val)) = 1 := by
      have hh (d : Bool) (k : Fin (side E χ d).length) :
          (List.finRange G.edges.length).countP
            (fun i => decide (vertexCode E G d i = k ∧ col i = c.val)) = 1 := by
        cases d
        · exact hcol.2.1 k c
        · exact hcol.2.2 k c
      exact hh s j
    have hp : (fun i => decide (vertexCode E G s i = j ∧ col i = c.val)) =
        (fun i => decide (((G.ends (original G i)).1 = v ∨ (G.ends (original G i)).2 = v) ∧ col i = c.val)) := by
      funext i; apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [vertexCode_incident E G s i j,hj]
    rw [hp] at hc; exact hc
  let color := fun e => if he : e ∈ G.edges then col (code G.edges e he) else 0
  have co (i : Fin G.edges.length) : color (original G i) = col i := by
    have hm : original G i ∈ G.edges := List.getElem_mem i.isLt
    simp only [color,hm,↓reduceDIte]
    congr 1
    apply Fin.ext
    exact G.distinct.idxOf_getElem i.val i.isLt
  refine ⟨color,?_,?_⟩
  · intro e he
    simp only [color,he,↓reduceDIte]
    exact hcol.1 _ (List.mem_finRange _)
  · intro v c
    have hg : (List.finRange G.edges.length).map (original G) = G.edges := by
      simp [original,List.finRange,List.map_ofFn,Function.comp_def]
    rw [←hg,List.countP_map]
    have hp : ((fun e => decide (((G.ends e).1 = v ∨ (G.ends e).2 = v) ∧ color e = c.val)) ∘ original G) =
        (fun i => decide (((G.ends (original G i)).1 = v ∨ (G.ends (original G i)).2 = v) ∧ col i = c.val)) := by
      funext i; simp only [Function.comp_apply,co]
    rw [hp]; exact hi v c

noncomputable def owner {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (i : Fin m) (o : Fin (M.word i).length) :
    Fin (chords (M.forest i)).length := Classical.choose (M.occurrence_unique i o)

theorem owner_unique {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (i : Fin m) (o : Fin (M.word i).length)
    (j : Fin (chords (M.forest i)).length)
    (hj : incident id o (chords (M.forest i))[j] = true) : owner M i o = j :=
  ((Classical.choose_spec (M.occurrence_unique i o)).2 j hj).symm

noncomputable def occurrenceLabel {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (color : M.Edge → Nat) (i : Fin m) (o : Fin (M.word i).length) : Nat :=
  color ⟨i,owner M i o⟩

theorem occurrence_endpoints {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (color : M.Edge → Nat) (i : Fin m)
    (j : Fin (chords (M.forest i)).length) :
    occurrenceLabel M color i (chords (M.forest i))[j].1 = color ⟨i,j⟩ ∧
    occurrenceLabel M color i (chords (M.forest i))[j].2 = color ⟨i,j⟩ := by
  have h1 := owner_unique M i (chords (M.forest i))[j].1 j (by simp [incident])
  have h2 := owner_unique M i (chords (M.forest i))[j].2 j (by simp [incident])
  exact ⟨congrArg (fun k => color ⟨i,k⟩) h1,congrArg (fun k => color ⟨i,k⟩) h2⟩

theorem occurrence_shared {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (color : M.Edge → Nat) (i : Fin m)
    (p : Fin (M.word i).length × Fin (M.word i).length) (hp : p ∈ chords (M.forest i)) :
    occurrenceLabel M color i p.1 = occurrenceLabel M color i p.2 := by
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hp
  have hh := occurrence_endpoints M color i ⟨j,hj⟩
  change occurrenceLabel M color i (chords (M.forest i))[j].1 = color ⟨i,⟨j,hj⟩⟩ ∧
    occurrenceLabel M color i (chords (M.forest i))[j].2 = color ⟨i,⟨j,hj⟩⟩ at hh
  rw [he] at hh
  exact hh.1.trans hh.2.symm

theorem labeled_incidence_count {O V : Type} [DecidableEq V]
    (χ : V → Bool) (mark : O → V) (labels : O → Nat)
    (F : NoncrossingMatch.Forest O (fun o => χ (mark o)))
    (hl : ∀ p ∈ chords F, labels p.1 = labels p.2) (v : V) (c : Nat) :
    (chords F).countP (fun p => decide ((mark p.1 = v ∨ mark p.2 = v) ∧ labels p.1 = c)) =
      F.flatten.countP (fun o => decide (mark o = v ∧ labels o = c)) := by
  induction F with
  | empty => rfl
  | concat u w ihu ihw =>
    have hu : ∀ p ∈ chords u, labels p.1 = labels p.2 := fun p hp => hl p (List.mem_append_left _ hp)
    have hw : ∀ p ∈ chords w, labels p.1 = labels p.2 := fun p hp => hl p (List.mem_append_right _ hp)
    simp only [chords,NoncrossingMatch.Forest.flatten,List.countP_append,ihu hu,ihw hw]
  | bracket x u y h ih =>
    have hu : ∀ p ∈ chords u, labels p.1 = labels p.2 := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have hxy : labels x = labels y := hl (x,y) (by simp [chords])
    have hne : mark x ≠ mark y := fun he => h (congrArg χ he)
    simp only [chords,NoncrossingMatch.Forest.flatten,List.countP_cons,List.countP_append,List.countP_nil,ih hu]
    by_cases hx : mark x = v <;> by_cases hy : mark y = v <;> by_cases hc : labels x = c
    · exact False.elim (hne (hx.trans hy.symm))
    · exact False.elim (hne (hx.trans hy.symm))
    all_goals simp [hx,hy,←hxy,hc] <;> omega

theorem occurrence_palette {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (M : Marks V χ m b) (color : M.Edge → Nat) (hc : PhysicalColoring M.graph color)
    (v : V) (c : Fin b) :
    ((List.finRange m).map (fun i => (List.finRange (M.word i).length).countP
      (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val)))).sum = 1 := by
  have hi (i : Fin m) :
      ((List.finRange (chords (M.forest i)).length).map (fun j => (⟨i,j⟩ : M.Edge))).countP
        (fun e => decide (((M.ends e).1 = v ∨ (M.ends e).2 = v) ∧ color e = c.val)) =
      (List.finRange (M.word i).length).countP
        (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val)) := by
    have hl := labeled_incidence_count χ (fun o => (M.word i)[o])
      (occurrenceLabel M color i) (M.forest i) (occurrence_shared M color i) v c.val
    rw [M.forest_flatten] at hl
    let p := fun z : Fin (M.word i).length × Fin (M.word i).length =>
      decide (((M.word i)[z.1] = v ∨ (M.word i)[z.2] = v) ∧ occurrenceLabel M color i z.1 = c.val)
    have hm : (List.finRange (chords (M.forest i)).length).map
        (fun j => (chords (M.forest i))[j]) = chords (M.forest i) := by
      simp [List.finRange,List.map_ofFn,Function.comp_def]
    have hmc := congrArg (List.countP p) hm
    rw [List.countP_map] at hmc
    rw [List.countP_map]
    have hp : ((fun e => decide (((M.ends e).1 = v ∨ (M.ends e).2 = v) ∧ color e = c.val)) ∘
        (fun j => (⟨i,j⟩ : M.Edge))) = p ∘ (fun j => (chords (M.forest i))[j]) := by
      funext j
      have he := (occurrence_endpoints M color i j).1
      exact (congrArg (fun k => decide (((M.ends (⟨i,j⟩ : M.Edge)).1 = v ∨
        (M.ends (⟨i,j⟩ : M.Edge)).2 = v) ∧ k = c.val)) he).symm
    rw [hp]
    exact hmc.trans hl
  have hg := hc.2 v c
  change M.edges.countP (fun e => decide (((M.ends e).1 = v ∨ (M.ends e).2 = v) ∧ color e = c.val)) = 1 at hg
  rw [Marks.edges,List.countP_flatMap] at hg
  have hp : (List.countP (fun e => decide (((M.ends e).1 = v ∨ (M.ends e).2 = v) ∧ color e = c.val)) ∘
      (fun i => (List.finRange (chords (M.forest i)).length).map (fun j => (⟨i,j⟩ : M.Edge)))) =
      (fun i => (List.finRange (M.word i).length).countP
        (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val))) := by
    funext i; exact hi i
  rw [hp] at hg
  exact hg

/-- Actual balanced marks with b occurrences at each physical vertex admit
shared chord labels and exactly one occurrence of each label there. -/
theorem exists_occurrence_coloring {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (E : Enumeration V) (M : Marks V χ m b) :
    ∃ color : M.Edge → Nat,
      (∀ i o, occurrenceLabel M color i o < b) ∧
      (∀ i p, p ∈ chords (M.forest i) →
        occurrenceLabel M color i p.1 = occurrenceLabel M color i p.2) ∧
      (∀ v (c : Fin b), ((List.finRange m).map (fun i => (List.finRange (M.word i).length).countP
        (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val)))).sum = 1) := by
  obtain ⟨color,hc⟩ := exists_physical_coloring E M.graph
  refine ⟨color,?_,occurrence_shared M color,occurrence_palette M color hc⟩
  intro i o
  exact hc.1 ⟨i,owner M i o⟩ (M.edges_complete _)

/-- Direct palette-valued occurrence labels for the noncrossing schedule. -/
theorem exists_palette_labels {V : Type} [DecidableEq V] {χ : V → Bool} {m b : Nat}
    (E : Enumeration V) (M : Marks V χ m b) :
    ∃ labels : (i : Fin m) → Fin (M.word i).length → Fin b,
      (∀ i p, p ∈ chords (M.forest i) → labels i p.1 = labels i p.2) ∧
      (∀ v (c : Fin b), ((List.finRange m).map (fun i => (List.finRange (M.word i).length).countP
        (fun o => decide ((M.word i)[o] = v ∧ labels i o = c)))).sum = 1) := by
  obtain ⟨color,hbound,hshared,hpalette⟩ := exists_occurrence_coloring E M
  let labels : (i : Fin m) → Fin (M.word i).length → Fin b :=
    fun i o => ⟨occurrenceLabel M color i o,hbound i o⟩
  refine ⟨labels,?_,?_⟩
  · intro i p hp; apply Fin.ext; exact hshared i p hp
  · intro v c
    have he (i : Fin m) : (fun o => decide ((M.word i)[o] = v ∧ labels i o = c)) =
        (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val)) := by
      funext o; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq,Fin.ext_iff]; rfl
    have hf : (fun i => (List.finRange (M.word i).length).countP
        (fun o => decide ((M.word i)[o] = v ∧ labels i o = c))) =
        (fun i => (List.finRange (M.word i).length).countP
          (fun o => decide ((M.word i)[o] = v ∧ occurrenceLabel M color i o = c.val))) := by
      funext i; rw [he i]
    rw [hf]
    exact hpalette v c

#print axioms exists_palette_labels
#print axioms exists_occurrence_coloring
#print axioms occurrence_shared
#print axioms labeled_incidence_count
#print axioms exists_physical_coloring
#print axioms graph_regular
end ErdePaths.ChordColor
