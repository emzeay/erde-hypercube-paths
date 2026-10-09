import ErdePaths.Compatible
import ErdePaths.SquareLift

namespace ErdePaths.ForkTransfer
open SquareLift

/-- Two normalized simple cycles with the opening fork at their common vertex 0.
The outgoing vertex of each cycle is absent from the other cycle. -/
structure ForkPair (V : Type) (L : Nat) where
  large : 3 ≤ L
  C : Fin L → V
  D : Fin L → V
  C_injective : Function.Injective C
  D_injective : Function.Injective D
  anchor : C ⟨0,by omega⟩ = D ⟨0,by omega⟩
  D_outside : ∀ i, D ⟨1,by omega⟩ ≠ C i
  C_outside : ∀ i, C ⟨1,by omega⟩ ≠ D i
  disjoint : ∀ i j, ¬SameEdge (C i,C (successor (by omega) i))
    (D j,D (successor (by omega) j))

theorem ForkPair.positive {V : Type} {L : Nat} (f : ForkPair V L) : 0 < L := by have := f.large; omega

def zero {L : Nat} (hL : 0 < L) : Fin L := ⟨0,hL⟩
def first {L : Nat} (h3 : 3 ≤ L) : Fin L := ⟨1,by omega⟩

/-- The opened list begins with the donated external vertex, then traverses
its own cycle backwards, ending at its own outgoing vertex 1. -/
def openedVertices {V : Type} {L : Nat} (hL : 0 < L) (cycle : Fin L → V) (external : V) :
    Fin (L+1) → V := Fin.cases external (fun r => cycle (backward hL (zero hL) r))

def ForkPair.vertices {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) : Fin (L+1) → V :=
  if p then openedVertices f.positive f.D (f.C (first f.large))
  else openedVertices f.positive f.C (f.D (first f.large))

def ForkPair.paths {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) : List V :=
  List.ofFn (f.vertices p)

/-- Generic vertex simplicity of a cycle opened by a vertex outside the cycle. -/
theorem openedVertices_injective {V : Type} {L : Nat} (hL : 0 < L)
    {cycle : Fin L → V} (hc : Function.Injective cycle) {external : V}
    (hext : ∀ i, external ≠ cycle i) : Function.Injective (openedVertices hL cycle external) := by
  intro s
  refine Fin.cases ?_ (fun i => ?_) s
  · intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · intro _; rfl
    · intro he
      exact False.elim (hext _ he)
  · intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · intro he
      exact False.elim (hext _ he.symm)
    · intro he
      have hh := backward_injective hL (zero hL) (hc he)
      exact congrArg Fin.succ hh

theorem ForkPair.vertices_injective {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) :
    Function.Injective (f.vertices p) := by
  cases p
  · exact openedVertices_injective f.positive f.C_injective f.D_outside
  · exact openedVertices_injective f.positive f.D_injective f.C_outside

theorem ForkPair.paths_length {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) :
    (f.paths p).length = L+1 := List.length_ofFn

theorem ForkPair.paths_nodup {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) :
    (f.paths p).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [ForkPair.paths,List.getElem_ofFn] at he
  exact congrArg (fun z : Fin (L+1) => z.val) (f.vertices_injective p he)

/-- Every retained step runs backwards along precisely one nonzero cycle arc. -/
theorem opened_step_retained {V : Type} {L : Nat} (hL : 0 < L)
    (cycle : Fin L → V) (external : V) (t : Fin L) (ht : t.val ≠ 0) :
    (openedVertices hL cycle external t.castSucc,openedVertices hL cycle external t.succ) =
    (cycle (successor hL (backward hL (zero hL) t)),cycle (backward hL (zero hL) t)) := by
  let prev : Fin L := ⟨t.val-1,by have := t.isLt; omega⟩
  have hi : prev.succ = t.castSucc := Fin.ext (by dsimp [prev,Fin.castSucc,Fin.castAdd,Fin.castLE]; omega)
  have hr : t.val-1+1 < L := by have := t.isLt; omega
  have hi' : (⟨t.val-1+1,hr⟩ : Fin L) = t := Fin.ext (by change t.val-1+1=t.val; omega)
  have hs : successor hL (backward hL (zero hL) t) = backward hL (zero hL) prev := by
    simpa [hi',prev] using successor_backward_step hL (zero hL) hr
  rw [← hi]
  simp only [openedVertices,Fin.cases_succ,hs]

theorem successor_zero {L : Nat} (h3 : 3 ≤ L) :
    successor (by omega) (zero (by omega)) = first h3 := by
  apply Fin.ext
  simp [successor,zero,first,Nat.mod_eq_of_lt (by omega : 1 < L)]

private theorem backward_nonzero {L : Nat} (hL : 0 < L) (t : Fin L) (ht : t.val ≠ 0) :
    (backward hL (zero hL) t).val ≠ 0 := by
  intro he
  have hh : backward hL (zero hL) t = backward hL (zero hL) (zero hL) := by
    have hzero : backward hL (zero hL) (zero hL) = zero hL := by simpa [zero] using backward_zero hL (zero hL)
    rw [hzero]
    exact Fin.ext he
  have hh' := congrArg Fin.val (backward_injective hL (zero hL) hh)
  exact ht hh'

/-- The only changed ownership is that the two zero arcs exchange paths. -/
def stepLabel {L : Nat} (hL : 0 < L) (p : Bool) (t : Fin L) : Fin L ⊕ Fin L :=
  if t.val = 0 then
    if p then .inl (zero hL) else .inr (zero hL)
  else if p then .inr (backward hL (zero hL) t) else .inl (backward hL (zero hL) t)

private def labelPosition {L : Nat} (hL : 0 < L) : Fin L ⊕ Fin L → Bool × Fin L
  | .inl i => if i.val=0 then (true,zero hL) else (false,backward hL (zero hL) i)
  | .inr i => if i.val=0 then (false,zero hL) else (true,backward hL (zero hL) i)

private theorem position_label {L : Nat} (hL : 0 < L) (p : Bool) (t : Fin L) :
    labelPosition hL (stepLabel hL p t) = (p,t) := by
  by_cases ht : t.val = 0
  · have he : t = zero hL := Fin.ext ht
    cases p <;> simp [stepLabel,labelPosition,he,zero]
  · have hn := backward_nonzero hL t ht
    cases p <;> simp [stepLabel,labelPosition,ht,hn,backward_inverse]

private theorem label_position {L : Nat} (hL : 0 < L) (e : Fin L ⊕ Fin L) :
    stepLabel hL (labelPosition hL e).1 (labelPosition hL e).2 = e := by
  cases e with
  | inl i =>
    by_cases hi : i.val=0
    · have he : i = zero hL := Fin.ext hi
      simp [stepLabel,labelPosition,he,zero]
    · have hn := backward_nonzero hL i hi
      simp [stepLabel,labelPosition,hi,hn,backward_inverse]
  | inr i =>
    by_cases hi : i.val=0
    · have he : i = zero hL := Fin.ext hi
      simp [stepLabel,labelPosition,he,zero]
    · have hn := backward_nonzero hL i hi
      simp [stepLabel,labelPosition,hi,hn,backward_inverse]

theorem stepLabel_injective {L : Nat} (hL : 0 < L) :
    Function.Injective (fun a : Bool × Fin L => stepLabel hL a.1 a.2) := by
  intro a b he
  have hh := congrArg (labelPosition hL) he
  simpa only [position_label] using hh

theorem stepLabel_surjective {L : Nat} (hL : 0 < L) :
    Function.Surjective (fun a : Bool × Fin L => stepLabel hL a.1 a.2) := by
  intro e
  exact ⟨labelPosition hL e,label_position hL e⟩

/-- Decoding labels yields the original cycles' edges in their original directions. -/
def ForkPair.decode {V : Type} {L : Nat} (f : ForkPair V L) : Fin L ⊕ Fin L → V × V
  | .inl i => (f.C i,f.C (successor f.positive i))
  | .inr i => (f.D i,f.D (successor f.positive i))

/-- Every transferred step is its original decoded edge in reverse direction. -/
theorem ForkPair.step_decodes {V : Type} {L : Nat} (f : ForkPair V L) (p : Bool) (t : Fin L) :
    (f.vertices p t.castSucc,f.vertices p t.succ) =
      ((f.decode (stepLabel f.positive p t)).2,(f.decode (stepLabel f.positive p t)).1) := by
  by_cases ht : t.val=0
  · have he : t = zero f.positive := Fin.ext ht
    have ha := f.anchor
    cases p <;> simp [ForkPair.vertices,openedVertices,stepLabel,ForkPair.decode,he,
      zero,first,backward_zero,successor,Nat.mod_eq_of_lt (by have := f.large; omega : 1 < L),Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,ha]
  · cases p
    · simpa [ForkPair.vertices,stepLabel,ht,ForkPair.decode] using
        opened_step_retained f.positive f.C (f.D (first f.large)) t ht
    · simpa [ForkPair.vertices,stepLabel,ht,ForkPair.decode] using
        opened_step_retained f.positive f.D (f.C (first f.large)) t ht

private theorem cycle_edge_injective {V : Type} {L : Nat} (h3 : 3 ≤ L)
    {cycle : Fin L → V} (hc : Function.Injective cycle) {i j : Fin L}
    (he : SameEdge (cycle i,cycle (successor (by omega) i))
      (cycle j,cycle (successor (by omega) j))) : i = j := by
  rcases he with he | he
  · exact hc (congrArg Prod.fst he)
  · have h1 := hc (congrArg Prod.fst he)
    have h2 := hc (congrArg Prod.snd he)
    rw [h1] at h2
    exact False.elim (successor_twice_ne (by omega) h3 j h2)

/-- Labels remain unique after forgetting orientation: cycle simplicity and
L≥3 prevent repeated cycle edges, while the fork hypothesis separates the cycles. -/
theorem ForkPair.decode_injective {V : Type} {L : Nat} (f : ForkPair V L)
    {e g : Fin L ⊕ Fin L} (he : SameEdge (f.decode e) (f.decode g)) : e = g := by
  cases e with
  | inl i =>
    cases g with
    | inl j => exact congrArg Sum.inl (cycle_edge_injective f.large f.C_injective he)
    | inr j => exact False.elim (f.disjoint i j he)
  | inr i =>
    cases g with
    | inl j => exact False.elim (f.disjoint j i (sameEdge_symm he))
    | inr j => exact congrArg Sum.inr (cycle_edge_injective f.large f.D_injective he)

/-- The exact host subgraph consisting of the two original cycles' undirected edges. -/
def ForkPair.unionRelation {V : Type} {L : Nat} (f : ForkPair V L) (u v : V) : Prop :=
  ∃ e : Fin L ⊕ Fin L, SameEdge (f.decode e) (u,v)

/-- Exact generic fork opening into two simple L-edge paths, retaining precisely
all original cycle edges and assigning every one uniquely. -/
def ForkPair.decomposition {V : Type} {L : Nat} (f : ForkPair V L) :
    GraphPathDecomposition V f.unionRelation L where
  Index := Bool
  indices := [false,true]
  vertices := f.vertices
  simple := fun p _ => f.vertices_injective p
  adjacent := by
    intro p _ t
    refine ⟨stepLabel f.positive p t,?_⟩
    exact sameEdge_symm (Or.inr (f.step_decodes p t))
  cover := by
    intro u v huv
    obtain ⟨e,he⟩ := huv
    obtain ⟨⟨p,t⟩,hlabel⟩ := stepLabel_surjective f.positive e
    refine ⟨p,by cases p <;> simp,t,?_⟩
    have hs : SameEdge (f.vertices p t.castSucc,f.vertices p t.succ) (f.decode e) := by
      exact Or.inr (by simpa [hlabel] using f.step_decodes p t)
    exact sameEdge_trans hs he
  unique := by
    intro p q _ _ t s he
    change SameEdge (f.vertices p t.castSucc,f.vertices p t.succ)
      (f.vertices q s.castSucc,f.vertices q s.succ) at he
    have ht : SameEdge (f.vertices p t.castSucc,f.vertices p t.succ)
        (f.decode (stepLabel f.positive p t)) := Or.inr (f.step_decodes p t)
    have hs : SameEdge (f.vertices q s.castSucc,f.vertices q s.succ)
        (f.decode (stepLabel f.positive q s)) := Or.inr (f.step_decodes q s)
    have hdecode := sameEdge_trans (sameEdge_symm ht) (sameEdge_trans he hs)
    have hlabel := f.decode_injective hdecode
    have hpos : (p,t) = (q,s) := stepLabel_injective f.positive hlabel
    exact ⟨congrArg Prod.fst hpos,congrArg Prod.snd hpos⟩

/-- An edge of the original union remains an edge in any symmetric host graph
containing the two cycles. Thus opening introduces no new hostgraph edge. -/
theorem ForkPair.union_in_host {V : Type} {L : Nat} (f : ForkPair V L)
    {R : V → V → Prop} (hsym : ∀ u v, R u v → R v u)
    (hC : ∀ i, R (f.C i) (f.C (successor f.positive i)))
    (hD : ∀ i, R (f.D i) (f.D (successor f.positive i)))
    {u v : V} (h : f.unionRelation u v) : R u v := by
  obtain ⟨e,he⟩ := h
  have hr : R (f.decode e).1 (f.decode e).2 := by
    cases e with
    | inl i => exact hC i
    | inr i => exact hD i
  rcases he with he | he
  · have hh := congrArg (fun z : V×V => R z.1 z.2) he
    exact hh.mp hr
  · have hh := congrArg (fun z : V×V => R z.2 z.1) he
    exact hh.mp (hsym _ _ hr)

/-- Actual list-step validity in any host graph containing the original cycles. -/
theorem ForkPair.paths_in_host {V : Type} {L : Nat} (f : ForkPair V L)
    {R : V → V → Prop} (hsym : ∀ u v, R u v → R v u)
    (hC : ∀ i, R (f.C i) (f.C (successor f.positive i)))
    (hD : ∀ i, R (f.D i) (f.D (successor f.positive i)))
    (p : Bool) (e : V×V) (he : e ∈ steps (f.paths p)) : R e.1 e.2 := by
  obtain ⟨t,ht,he⟩ := List.mem_iff_getElem.mp he
  have ht' : t < L := by
    simp only [steps,List.length_zip,List.length_tail,ForkPair.paths,List.length_ofFn] at ht
    omega
  have hh : f.unionRelation
      (f.vertices p (⟨t,ht'⟩ : Fin L).castSucc) (f.vertices p (⟨t,ht'⟩ : Fin L).succ) :=
    ⟨stepLabel f.positive p ⟨t,ht'⟩,sameEdge_symm (Or.inr (f.step_decodes p ⟨t,ht'⟩))⟩
  have he' : (f.vertices p ⟨t,by omega⟩,f.vertices p ⟨t+1,by omega⟩) = e := by
    simpa only [steps,List.getElem_zip,List.getElem_tail,ForkPair.paths,List.getElem_ofFn] using he
  apply f.union_in_host hsym hC hD
  rw [← congrArg Prod.fst he',← congrArg Prod.snd he']
  simpa [Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using hh

/-- Generic undirected edge membership for actual finite vertex lists. -/
def ListUsesEdge {V : Type} (path : List V) (u v : V) : Prop :=
  (u,v) ∈ steps path ∨ (v,u) ∈ steps path

private theorem mem_steps_ofFn {V : Type} {L : Nat} (vertices : Fin (L+1) → V) (e : V×V) :
    e ∈ steps (List.ofFn vertices) ↔ ∃ j : Fin L, (vertices j.castSucc,vertices j.succ) = e := by
  constructor
  · intro he
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp he
    have hj' : j < L := by
      simp only [steps,List.length_zip,List.length_tail,List.length_ofFn] at hj
      omega
    refine ⟨⟨j,hj'⟩,?_⟩
    simpa only [steps,List.getElem_zip,List.getElem_tail,List.getElem_ofFn,
      Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using he
  · rintro ⟨j,he⟩
    apply List.mem_iff_getElem.mpr
    have hj : j.val < (steps (List.ofFn vertices)).length := by
      simp only [steps,List.length_zip,List.length_tail,List.length_ofFn]
      have := j.isLt
      omega
    refine ⟨j.val,hj,?_⟩
    simpa only [steps,List.getElem_zip,List.getElem_tail,List.getElem_ofFn,
      Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ] using he

private theorem list_uses_iff_position {V : Type} {L : Nat}
    (vertices : Fin (L+1) → V) (u v : V) :
    ListUsesEdge (List.ofFn vertices) u v ↔
      ∃ j : Fin L, SameEdge (vertices j.castSucc,vertices j.succ) (u,v) := by
  unfold ListUsesEdge
  rw [mem_steps_ofFn,mem_steps_ofFn]
  constructor
  · rintro (⟨j,he⟩ | ⟨j,he⟩)
    · exact ⟨j,Or.inl he⟩
    · exact ⟨j,Or.inr he⟩
  · rintro ⟨j,he | he⟩
    · exact Or.inl ⟨j,he⟩
    · exact Or.inr ⟨j,he⟩

/-- Exact edge preservation stated directly for the two output vertex lists. -/
theorem ForkPair.list_edge_coverage {V : Type} {L : Nat} (f : ForkPair V L) (u v : V) :
    f.unionRelation u v ↔ ∃ p : Bool, ListUsesEdge (f.paths p) u v := by
  constructor
  · rintro ⟨e,he⟩
    obtain ⟨⟨p,t⟩,hlabel⟩ := stepLabel_surjective f.positive e
    refine ⟨p,(list_uses_iff_position (f.vertices p) u v).mpr ⟨t,?_⟩⟩
    exact sameEdge_trans (Or.inr (by simpa [hlabel] using f.step_decodes p t)) he
  · rintro ⟨p,hp⟩
    obtain ⟨t,ht⟩ := (list_uses_iff_position (f.vertices p) u v).mp hp
    refine ⟨stepLabel f.positive p t,?_⟩
    exact sameEdge_trans (sameEdge_symm (Or.inr (f.step_decodes p t))) ht

/-- Unique owner path for every edge of the actual output lists. Unique positions
inside that path are already part of `decomposition`. -/
theorem ForkPair.list_edge_unique {V : Type} {L : Nat} (f : ForkPair V L)
    {p q : Bool} {u v : V} (hp : ListUsesEdge (f.paths p) u v)
    (hq : ListUsesEdge (f.paths q) u v) : p = q := by
  obtain ⟨t,ht⟩ := (list_uses_iff_position (f.vertices p) u v).mp hp
  obtain ⟨s,hs⟩ := (list_uses_iff_position (f.vertices q) u v).mp hq
  have hdecode : SameEdge (f.decode (stepLabel f.positive p t))
      (f.decode (stepLabel f.positive q s)) :=
    sameEdge_trans (sameEdge_symm (Or.inr (f.step_decodes p t)))
      (sameEdge_trans ht (sameEdge_trans (sameEdge_symm hs) (Or.inr (f.step_decodes q s))))
  have hpos : (p,t) = (q,s) := stepLabel_injective f.positive (f.decode_injective hdecode)
  exact congrArg Prod.fst hpos

/-- Both opened paths have the same endpoint pair, in opposite directions. -/
theorem ForkPair.endpoints {V : Type} {L : Nat} (f : ForkPair V L) :
    f.vertices false ⟨0,by omega⟩ = f.D (first f.large) ∧
    f.vertices false ⟨L,by omega⟩ = f.C (first f.large) ∧
    f.vertices true ⟨0,by omega⟩ = f.C (first f.large) ∧
    f.vertices true ⟨L,by omega⟩ = f.D (first f.large) := by
  have hi : (⟨L-1,by have := f.large; omega⟩ : Fin L).succ =
      (⟨L,by omega⟩ : Fin (L+1)) := Fin.ext (by dsimp; have := f.large; omega)
  have hlast : backward f.positive (zero f.positive) ⟨L-1,by have := f.large; omega⟩ = first f.large := by
    rw [backward_last]
    exact successor_zero f.large
  constructor
  · rfl
  constructor
  · rw [← hi]
    simp [ForkPair.vertices,openedVertices,hlast]
  constructor
  · rfl
  · rw [← hi]
    simp [ForkPair.vertices,openedVertices,hlast]

/-- Each actual output list has L consecutive edges, hence the two lists have 2L steps. -/
theorem ForkPair.edge_counts {V : Type} {L : Nat} (f : ForkPair V L) :
    (steps (f.paths false)).length = L ∧ (steps (f.paths true)).length = L ∧
    ([f.paths false,f.paths true].flatMap steps).length = 2*L := by
  simp [steps,ForkPair.paths,List.length_zip,List.length_ofFn,Nat.two_mul]

#print axioms ForkPair.list_edge_coverage
#print axioms ForkPair.list_edge_unique
#print axioms ForkPair.decomposition
#print axioms ForkPair.paths_in_host
#print axioms openedVertices_injective
end ErdePaths.ForkTransfer
