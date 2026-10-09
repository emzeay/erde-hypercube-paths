import ErdePaths.HamiltonData
import ErdePaths.HamiltonScan

namespace ErdePaths.HamiltonNormalize
open SquareLift HamiltonData HamiltonScan

theorem forward_successor {N} (hN : 0<N) (a t : Fin N) :
    forward hN a (successor hN t) = successor hN (forward hN a t) := by
  apply Fin.ext
  simp only [forward,successor]
  rw [Nat.add_mod_mod,Nat.mod_add_mod,Nat.add_assoc]

theorem unrotate_rotate {N} (hN : 0<N) (a t : Fin N) :
    backward hN (forward hN a t) a = t := by
  apply forward_injective hN a
  exact forward_inverse hN a (forward hN a t)

/-- Rotation of an actual Hamilton tour with its actual inverse and edges. -/
def rotate {V R N hN} (C : CycleData V R N hN) (a : Fin N) :
    CycleData V R N hN where
  cycle t := C.cycle (forward hN a t)
  position v := backward hN (C.position v) a
  position_cycle t := by simp only [C.position_cycle,unrotate_rotate]
  cycle_position v := by rw [forward_inverse,C.cycle_position]
  adjacent t := by rw [forward_successor]; exact C.adjacent _

/-- The selected edge is literally the closing edge of this rotated tour. -/
def closeSelected {V R N hN} (C : CycleData V R N hN) (t : Fin N) :
    CycleData V R N hN := rotate C (successor hN t)

theorem closeSelected_zero {V R N hN} (C : CycleData V R N hN) (t : Fin N) :
    (closeSelected C t).cycle ⟨0,hN⟩ = C.cycle (successor hN t) := by
  simp [closeSelected,rotate,forward_zero]

theorem closeSelected_last {V R N hN} (C : CycleData V R N hN) (t : Fin N) :
    (closeSelected C t).cycle ⟨N-1,by omega⟩ = C.cycle t := by
  simp [closeSelected,rotate,forward_last,predecessor_successor]

def endpoint {V R m N hN} (cycles : Fin m → CycleData V R N hN)
    (selected : Fin m → Fin N) (q : Fin m × Bool) : V :=
  if q.2 then (cycles q.1).cycle (successor hN (selected q.1))
    else (cycles q.1).cycle (selected q.1)

theorem endpoint_mem_pair {V R m N hN} (cycles : Fin m → CycleData V R N hN)
    (selected : Fin m → Fin N) (i : Fin m) (b : Bool) :
    endpoint cycles selected (i,b) ∈
      [(cycles i).cycle (selected i),(cycles i).cycle (successor hN (selected i))] := by
  cases b <;> simp [endpoint]

/-- No injective-endpoint assumption: it follows from the greedy theorem's
literal flattened endpoint list. -/
theorem endpoint_injective {V R m N hN} (cycles : Fin m → CycleData V R N hN)
    (selected : Fin m → Fin N) (hn : (endpointList cycles selected).Nodup) :
    Function.Injective (endpoint cycles selected) := by
  have hp := List.pairwise_flatMap.mp hn
  have hcross (i j : Fin m) (hij : i.val<j.val) :
      ∀ v ∈ [(cycles i).cycle (selected i),(cycles i).cycle (successor hN (selected i))],
      ∀ w ∈ [(cycles j).cycle (selected j),(cycles j).cycle (successor hN (selected j))],
        v ≠ w := by
    have hh := hp.2.rel_getElem_of_lt
      (by simp) (by simp) hij
    simpa using hh
  intro q r he
  rcases q with ⟨i,b⟩
  rcases r with ⟨j,c⟩
  have hi : i=j := by
    by_cases hij : i.val<j.val
    · exact False.elim (hcross i j hij _ (endpoint_mem_pair cycles selected i b)
        _ (endpoint_mem_pair cycles selected j c) he)
    by_cases hji : j.val<i.val
    · exact False.elim (hcross j i hji _ (endpoint_mem_pair cycles selected j c)
        _ (endpoint_mem_pair cycles selected i b) he.symm)
    exact Fin.ext (by omega)
  subst j
  have hs := hp.1 i (by simp)
  have hne : (cycles i).cycle (selected i) ≠
      (cycles i).cycle (successor hN (selected i)) := by simpa using hs
  cases b <;> cases c
  · rfl
  · exact False.elim (hne (by simpa [endpoint] using he))
  · exact False.elim (hne (by simpa [endpoint] using he.symm))
  · rfl

theorem position_injective {V R N hN} (C : CycleData V R N hN) :
    Function.Injective C.position := by
  intro v w h
  simpa only [C.cycle_position] using congrArg C.cycle h

def raw {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (q : Fin k × Bool) : Nat :=
  ((closeSelected (cycles 0) (selected 0)).position
    (endpoint cycles selected (q.1.succ,q.2))).val

theorem raw_injective {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup) :
    Function.Injective (raw cycles selected) := by
  intro q r he
  have hp : (closeSelected (cycles 0) (selected 0)).position
      (endpoint cycles selected (q.1.succ,q.2)) =
      (closeSelected (cycles 0) (selected 0)).position
      (endpoint cycles selected (r.1.succ,r.2)) := Fin.ext he
  have hh := endpoint_injective cycles selected hn
    (position_injective _ hp)
  apply Prod.ext
  · have hv := congrArg (fun z : Fin (k+1) × Bool => z.1.val) hh
    exact Fin.ext (by simpa using hv)
  · exact congrArg (fun z : Fin (k+1) × Bool => z.2) hh

theorem raw_internal {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (q : Fin k × Bool) : 0<raw cycles selected q ∧ raw cycles selected q<N-1 := by
  let C := closeSelected (cycles 0) (selected 0)
  let v := endpoint cycles selected (q.1.succ,q.2)
  have hb : raw cycles selected q < N := (C.position v).isLt
  have hzero : raw cycles selected q ≠ 0 := by
    intro hz
    have hp : C.position v = ⟨0,hN⟩ := Fin.ext hz
    have hv : v = (cycles 0).cycle (successor hN (selected 0)) := by
      have hh := congrArg C.cycle hp
      rw [C.cycle_position] at hh
      exact hh.trans (closeSelected_zero _ _)
    have hi := endpoint_injective cycles selected hn
      (show endpoint cycles selected (q.1.succ,q.2)=endpoint cycles selected (0,true) from
        by simpa [endpoint,v] using hv)
    have hh := congrArg (fun z : Fin (k+1) × Bool => z.1.val) hi
    simp at hh
  have hlast : raw cycles selected q ≠ N-1 := by
    intro hz
    have hp : C.position v = ⟨N-1,by omega⟩ := Fin.ext hz
    have hv : v = (cycles 0).cycle (selected 0) := by
      have hh := congrArg C.cycle hp
      rw [C.cycle_position] at hh
      exact hh.trans (closeSelected_last _ _)
    have hi := endpoint_injective cycles selected hn
      (show endpoint cycles selected (q.1.succ,q.2)=endpoint cycles selected (0,false) from
        by simpa [endpoint,v] using hv)
    have hh := congrArg (fun z : Fin (k+1) × Bool => z.1.val) hi
    simp at hh
  omega

def sortCode {k} (f : Fin k × Bool → Nat) (q : Fin k × Bool) : Fin k × Bool :=
  (q.1, if f (q.1,false)<f (q.1,true) then q.2 else !q.2)

theorem sortCode_injective {k} (f : Fin k × Bool → Nat) :
    Function.Injective (sortCode f) := by
  intro q r he
  have hi := congrArg (fun z : Fin k × Bool => z.1) he
  change q.1=r.1 at hi
  rcases q with ⟨i,b⟩
  rcases r with ⟨j,c⟩
  change i=j at hi
  subst j
  have hb := congrArg Prod.snd he
  by_cases h : f (i,false)<f (i,true)
  · simpa [sortCode,h] using congrArg (fun b => (i,b)) hb
  · cases b <;> cases c <;> simp_all [sortCode]

def sorted {k} (f : Fin k × Bool → Nat) (q : Fin k × Bool) : Nat := f (sortCode f q)

theorem sorted_injective {k} (f : Fin k × Bool → Nat) (hf : Function.Injective f) :
    Function.Injective (sorted f) := fun _ _ h => sortCode_injective f (hf h)

theorem sorted_ordered {k} (f : Fin k × Bool → Nat) (hf : Function.Injective f)
    (i : Fin k) : sorted f (i,false)<sorted f (i,true) := by
  have hne : f (i,false)≠f (i,true) := by
    intro he
    have hh := congrArg Prod.snd (hf he)
    simp at hh
  by_cases h : f (i,false)<f (i,true)
  · simp [sorted,sortCode,h]
  · simp [sorted,sortCode,h]
    omega

noncomputable def lookup {k} (f : Fin k × Bool → Nat) (j : Nat) : Kind k :=
  if h : ∃ i, f (i,false)=j then .lower h.choose
  else if h : ∃ i, f (i,true)=j then .upper h.choose else .ordinary

theorem lookup_lower {k} (f : Fin k × Bool → Nat) (hf : Function.Injective f)
    (i : Fin k) : lookup f (f (i,false)) = .lower i := by
  have h : ∃ l, f (l,false)=f (i,false) := ⟨i,rfl⟩
  have hi : h.choose=i := congrArg (fun z : Fin k × Bool => z.1) (hf h.choose_spec)
  simp only [lookup,dite_eq_left h,hi]

theorem lookup_upper {k} (f : Fin k × Bool → Nat) (hf : Function.Injective f)
    (i : Fin k) : lookup f (f (i,true)) = .upper i := by
  have hn : ¬∃ l, f (l,false)=f (i,true) := by
    rintro ⟨l,hl⟩
    have hh := congrArg (fun z : Fin k × Bool => z.2) (hf hl)
    simp at hh
  have h : ∃ l, f (l,true)=f (i,true) := ⟨i,rfl⟩
  have hi : h.choose=i := congrArg (fun z : Fin k × Bool => z.1) (hf h.choose_spec)
  simp only [lookup,dite_eq_right hn,dite_eq_left h,hi]

theorem lookup_lower_index {k} (f : Fin k × Bool → Nat) (j : Nat) (i : Fin k)
    (h : lookup f j = .lower i) : j=f (i,false) := by
  unfold lookup at h
  split at h
  · rename_i he
    have hi : he.choose=i := Kind.lower.inj h
    have hh := he.choose_spec
    rw [hi] at hh
    exact hh.symm
  · split at h <;> contradiction

theorem lookup_upper_index {k} (f : Fin k × Bool → Nat) (j : Nat) (i : Fin k)
    (h : lookup f j = .upper i) : j=f (i,true) := by
  unfold lookup at h
  split at h
  · contradiction
  · split at h
    · rename_i hn he
      have hi : he.choose=i := Kind.upper.inj h
      have hh := he.choose_spec
      rw [hi] at hh
      exact hh.symm
    · contradiction

noncomputable def matchingFromEndpoints {N k} (f : Fin k × Bool → Nat)
    (hf : Function.Injective f) (hinterior : ∀ q, 0<f q ∧ f q<N-1)
    (horder : ∀ i, f (i,false)<f (i,true)) : Matching N k where
  lower i := f (i,false)
  upper i := f (i,true)
  kind := lookup f
  lower_kind := lookup_lower f hf
  upper_kind := lookup_upper f hf
  kind_lower := lookup_lower_index f
  kind_upper := lookup_upper_index f
  lower_pos i := (hinterior (i,false)).1
  ordered := horder
  upper_bound i := (hinterior (i,true)).2

/-- The actual bridge from selected graph edges to the checked scan. -/
noncomputable def normalizedMatching {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup) :
    Matching N k := matchingFromEndpoints (sorted (raw cycles selected))
      (sorted_injective _ (raw_injective cycles selected hn))
      (fun q => raw_internal cycles selected hn (sortCode (raw cycles selected) q))
      (sorted_ordered _ (raw_injective cycles selected hn))

/-- Selection and endpoint normalization are available directly from an
actual old decomposition under the proved greedy room bound. -/
theorem normalizedMatching_exists {V R k N hN}
    (D : DecompositionData V R (k+1) N hN) (hroom : 4*k<N) :
    ∃ selected : Fin (k+1) → Fin N,
      ∃ _hn : (endpointList D.cycles selected).Nodup,
        Nonempty (Matching N k) := by
  obtain ⟨selected,hn⟩ := decomposition_select_disjoint_edges D (by simpa using hroom)
  exact ⟨selected,hn,⟨normalizedMatching D.cycles selected hn⟩⟩

theorem upper_injective {N k} (M : Matching N k) : Function.Injective M.upper := by
  intro i j h
  have hh := congrArg M.kind h
  rw [M.upper_kind,M.upper_kind] at hh
  exact Kind.upper.inj hh

theorem isUpper_iff {N k} (M : Matching N k) (j : Nat) :
    isUpper (M.kind j)=true ↔ ∃ i, M.upper i=j := by
  constructor
  · intro h
    cases hk : M.kind j with
    | ordinary => simp [hk,isUpper] at h
    | lower i => simp [hk,isUpper] at h
    | upper i => exact ⟨i,(M.kind_upper j i hk).symm⟩
  · rintro ⟨i,rfl⟩; simp [M.upper_kind,isUpper]

theorem uppers_nodup {N k} (M : Matching N k) :
    ((List.finRange k).map M.upper).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.nodup_finRange k).imp
  intro i j hne he
  exact hne (upper_injective M he)

theorem filtered_uppers_perm {N k} (M : Matching N k) :
    ((middle N).filter fun j => isUpper (M.kind j)).Perm
      ((List.finRange k).map M.upper) := by
  have hf : ((middle N).filter fun j => isUpper (M.kind j)).Nodup :=
    (middle_nodup N).filter _
  apply (List.perm_ext_iff_of_nodup hf (uppers_nodup M)).mpr
  intro j
  simp only [List.mem_filter,List.mem_map,List.mem_finRange,true_and,isUpper_iff]
  constructor
  · rintro ⟨_,i,hi⟩; exact ⟨i,hi⟩
  · rintro ⟨i,rfl⟩
    refine ⟨middle_mem.mpr ⟨?_,M.upper_bound i⟩,i,rfl⟩
    have hl := M.lower_pos i
    have ho := M.ordered i
    omega

/-- Exactly k distinct upper endpoints are scanned; no endpoint count input. -/
theorem upper_count {N k} (M : Matching N k) :
    ((middle N).filter fun j => isUpper (M.kind j)).length=k := by
  have hh := (filtered_uppers_perm M).length_eq
  simpa using hh

def vertexAt {V R N hN} (C : CycleData V R N hN) (j : Nat) : V :=
  C.cycle ⟨j%N,Nat.mod_lt _ hN⟩

theorem raw_vertex {V R k N hN} (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (q : Fin k × Bool) :
    vertexAt (closeSelected (cycles 0) (selected 0)) (raw cycles selected q) =
      endpoint cycles selected (q.1.succ,q.2) := by
  unfold vertexAt raw
  have hp : (⟨((closeSelected (cycles 0) (selected 0)).position
      (endpoint cycles selected (q.1.succ,q.2))).val%N,Nat.mod_lt _ hN⟩ : Fin N) =
      (closeSelected (cycles 0) (selected 0)).position
        (endpoint cycles selected (q.1.succ,q.2)) :=
    Fin.ext (Nat.mod_eq_of_lt ((closeSelected (cycles 0) (selected 0)).position
      (endpoint cycles selected (q.1.succ,q.2))).isLt)
  rw [hp]
  exact (closeSelected (cycles 0) (selected 0)).cycle_position _

/-- Sorting the other endpoints preserves their actual selected graph edge. -/
theorem normalized_selected_adjacent {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (hsym : ∀ a b, R a b → R b a) (i : Fin k) :
    R (vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).lower i))
      (vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).upper i)) := by
  change R (vertexAt _ (sorted (raw cycles selected) (i,false)))
    (vertexAt _ (sorted (raw cycles selected) (i,true)))
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [sorted,sortCode,ite_eq_left h]
    rw [raw_vertex,raw_vertex]
    exact (cycles i.succ).adjacent (selected i.succ)
  · simp only [sorted,sortCode,ite_eq_right h,Bool.not_false,Bool.not_true]
    rw [raw_vertex,raw_vertex]
    exact hsym _ _ ((cycles i.succ).adjacent (selected i.succ))

/-- The oriented normalization changes only the order of the two endpoints,
so the undirected edge ledger can use the original selected factor edge. -/
theorem normalized_selected_sameEdge {V R k N hN}
    (cycles : Fin (k+1) → CycleData V R N hN)
    (selected : Fin (k+1) → Fin N) (hn : (endpointList cycles selected).Nodup)
    (i : Fin k) : SameEdge
      (vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).lower i),
       vertexAt (closeSelected (cycles 0) (selected 0))
        ((normalizedMatching cycles selected hn).upper i))
      ((cycles i.succ).cycle (selected i.succ),
       (cycles i.succ).cycle (successor hN (selected i.succ))) := by
  change SameEdge (vertexAt _ (sorted (raw cycles selected) (i,false)),
      vertexAt _ (sorted (raw cycles selected) (i,true))) _
  by_cases h : raw cycles selected (i,false)<raw cycles selected (i,true)
  · simp only [sorted,sortCode,ite_eq_left h]
    rw [raw_vertex,raw_vertex]
    exact Or.inl rfl
  · simp only [sorted,sortCode,ite_eq_right h,Bool.not_false,Bool.not_true]
    rw [raw_vertex,raw_vertex]
    exact Or.inr rfl

theorem rotate_step {V R N hN} (C : CycleData V R N hN) (a t : Fin N) :
    ((rotate C a).cycle t,(rotate C a).cycle (successor hN t)) =
      (C.cycle (forward hN a t),C.cycle (successor hN (forward hN a t))) := by
  simp only [rotate,forward_successor]

def processed (N : Nat) : List Nat := (List.range (N-2)).map (fun a => N-2-a)

theorem processed_perm (N : Nat) : (processed N).Perm (middle N) := by
  have hn : (processed N).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_range (n := N-2)).imp_of_mem
    intro a b ha hb hne he
    have ha := List.mem_range.mp ha
    have hb := List.mem_range.mp hb
    exact hne (by omega)
  apply (List.perm_ext_iff_of_nodup hn (middle_nodup N)).mpr
  intro j
  simp only [processed,List.mem_map,List.mem_range,middle_mem]
  constructor
  · rintro ⟨a,ha,rfl⟩; omega
  · intro ⟨hp,hb⟩; exact ⟨N-2-j,by omega,by omega⟩

private theorem filter_complement_length {V : Type} (p : V → Bool) (l : List V) :
    (l.filter p).length + (l.filter fun v => !(p v)).length = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => cases hp : p a <;> simp [hp] <;> omega

/-- The exact number of state toggles is middle-count minus upper-count. -/
theorem toggle_count_total {N k} (M : Matching N k) :
    toggleCount M (N-2)+k=N-2 := by
  have hp := ((processed_perm N).filter (fun j => !(isUpper (M.kind j)))).length_eq
  simp only [processed,List.filter_map,List.length_map,Function.comp_def] at hp
  have hc := filter_complement_length (fun j => isUpper (M.kind j)) (middle N)
  rw [upper_count] at hc
  have hl : (middle N).length=N-2 := by simp [middle]
  rw [hl] at hc
  rw [toggleCount_filter]
  change ((List.range (N-2)).filter fun a => !(isUpper (M.kind (N-2-a)))).length+k=N-2
  rw [hp]
  omega

theorem state_final_count {N k} (M : Matching N k) :
    state M 0 = decide ((N-2-k)%2=1) := by
  have hc := toggle_count_total M
  unfold state
  simp only [Nat.sub_zero]
  rw [stateAux_parity]
  have he : toggleCount M (N-2)=N-2-k := by omega
  rw [he]

/-- For an even parent cycle, numeric final row is 2 exactly when the old
number k+1 of Hamilton factors is even, as required by the boundary repairs. -/
theorem state_final_factor_parity {N k} (M : Matching N k) (hN : 2≤N)
    (heven : N%2=0) : state M 0 = decide ((k+1)%2=0) := by
  have hc := toggle_count_total M
  rw [state_final_count]
  have hi : (N-2-k)%2=1 ↔ (k+1)%2=0 := by omega
  simp only [hi]

#print axioms normalizedMatching
#print axioms normalizedMatching_exists
#print axioms normalized_selected_adjacent
#print axioms normalized_selected_sameEdge
#print axioms upper_count
#print axioms state_final_count
#print axioms state_final_factor_parity

#print axioms endpoint_injective
#print axioms raw_internal
end ErdePaths.HamiltonNormalize
