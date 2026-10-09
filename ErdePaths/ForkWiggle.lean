import ErdePaths.SubdividedWiggle
import ErdePaths.ForkTransfer

namespace ErdePaths.ForkWiggle
open SquareLift Wiggle SubdividedWiggle ForkTransfer

abbrev cycleLength (a B s : Nat) := a*(B*(s+1))

theorem length_large {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (hs : 2≤s) : 3≤cycleLength a B s := by
  have hm : 2*(4*3)≤a*(B*(s+1)) := Nat.mul_le_mul ha (Nat.mul_le_mul hB (by omega))
  unfold cycleLength
  omega

theorem backward_successor {N : Nat} (hN : 0<N) (i t : Fin N) :
    successor hN (backward hN i (successor hN t))=backward hN i t := by
  by_cases ht : t.val+1<N
  · have he : successor hN t=(⟨t.val+1,ht⟩ : Fin N) := Fin.ext (Nat.mod_eq_of_lt ht)
    rw [he]
    exact successor_backward_step hN i ht
  · have hlast : t.val=N-1 := by have := t.isLt; omega
    have ht' : t=(⟨N-1,by omega⟩ : Fin N) := Fin.ext hlast
    have hz : successor hN t=(⟨0,hN⟩ : Fin N) := by
      apply Fin.ext
      have he : t.val+1=N := by have := t.isLt; omega
      simp [successor,he]
    rw [hz,backward_zero,ht',backward_last]

def anchorIndex {a B s : Nat} (ha : 0<a) (hB : 0<B) : Fin (cycleLength a B s) :=
  expandedIndex (⟨a-1,by omega⟩,⟨0,hB⟩,(⟨s,by omega⟩ : Fin (s+1)))

def leftIndex {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) : Fin (cycleLength a B s) :=
  expandedIndex (⟨a-1,by omega⟩,⟨0,hB⟩,(⟨s-1,by omega⟩ : Fin (s+1)))

def C {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) := expandedCycle ha hB hs

def D {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (t : Fin (cycleLength a B s)) :=
  translatedExpandedCycle ha hB hs
    (backward (Nat.mul_pos ha (Nat.mul_pos hB (show 0<s+1 by omega))) (anchorIndex ha hB) t)

theorem expanded_at_index {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1)) : expandedCycle ha hB hs (expandedIndex p)=expandedVertex ha hs p := by
  unfold expandedCycle
  rw [expandedIndex_inverse]

theorem translated_at_index {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    (p : Fin a × Fin B × Fin (s+1)) :
    translatedExpandedCycle ha hB hs (expandedIndex p)=translatedExpandedVertex ha hs p := by
  unfold translatedExpandedCycle
  rw [expandedIndex_inverse]

theorem predecessor_anchor {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s) :
    predecessor (Nat.mul_pos ha (Nat.mul_pos hB (show 0<s+1 by omega))) (anchorIndex (s := s) ha hB)=leftIndex ha hB hs := by
  have hL : 0<cycleLength a B s := Nat.mul_pos ha (Nat.mul_pos hB (by omega))
  have hi := (leftIndex ha hB hs).isLt
  have hai := (anchorIndex (s := s) ha hB).isLt
  apply Fin.ext
  simp only [predecessor,anchorIndex,leftIndex,expandedIndex,Nat.zero_mul,Nat.zero_add]
  change ((cycleLength a B s)-1+((B*(s+1))*(a-1)+s))%(cycleLength a B s)=
    (B*(s+1))*(a-1)+(s-1)
  simp only [leftIndex,expandedIndex,Nat.zero_mul,Nat.zero_add] at hi
  have he : cycleLength a B s-1+((B*(s+1))*(a-1)+s)=
      cycleLength a B s+((B*(s+1))*(a-1)+(s-1)) := by omega
  simp [he,Nat.mod_eq_of_lt hi]

theorem C_zero {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 0<s) :
    C ha (by omega) hs ⟨0,Nat.mul_pos ha (Nat.mul_pos (show 0<B by omega) (by omega))⟩=
      anchor (B := B) ha (by omega) hs := by
  have hi : expandedIndex (⟨0,ha⟩,⟨0,show 0<B by omega⟩,(⟨0,by omega⟩ : Fin (s+1)))=
      (⟨0,Nat.mul_pos ha (Nat.mul_pos (show 0<B by omega) (by omega))⟩ : Fin (cycleLength a B s)) := by apply Fin.ext; simp [expandedIndex]
  unfold C
  rw [←hi,expanded_at_index]
  exact anchor_occurs_zero ha hB hs

theorem C_first {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (hs : 2≤s) :
    C (show 0<a by omega) (by omega) (by omega) (⟨1,by have := length_large (a := a) (B := B) (s := s) ha hB hs; omega⟩ : Fin (cycleLength a B s))=
      rightNeighbor (B := B) (show 0<a by omega) (by omega) hs := by
  have hi : expandedIndex (⟨0,show 0<a by omega⟩,⟨0,show 0<B by omega⟩,(⟨1,by omega⟩ : Fin (s+1)))=
      (⟨1,by have := length_large ha hB hs; omega⟩ : Fin (cycleLength a B s)) := by apply Fin.ext; simp [expandedIndex]
  unfold C
  rw [←hi,expanded_at_index]
  exact rightNeighbor_occurs (show 0<a by omega) hB hs

theorem D_zero {a B s : Nat} (ha : 0<a) (hB : 4≤B) (hs : 0<s) :
    D ha (by omega) hs ⟨0,Nat.mul_pos ha (Nat.mul_pos (show 0<B by omega) (by omega))⟩=
      anchor (B := B) ha (by omega) hs := by
  unfold D
  rw [backward_zero]
  unfold anchorIndex
  rw [translated_at_index]
  exact anchor_occurs_one ha hB hs

theorem D_first {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (hs : 2≤s) :
    D (show 0<a by omega) (by omega) (by omega) (⟨1,by have := length_large (a := a) (B := B) (s := s) ha hB hs; omega⟩ : Fin (cycleLength a B s))=
      leftNeighbor (B := B) (show 0<a by omega) (by omega) hs := by
  unfold D
  have he : backward (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega)))
      (anchorIndex (s := s) (show 0<a by omega) (show 0<B by omega)) (⟨1,by have := length_large (a := a) (B := B) (s := s) ha hB hs; omega⟩ : Fin (cycleLength a B s))=
      predecessor (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (show 0<s+1 by omega))) (anchorIndex (show 0<a by omega) (show 0<B by omega)) := rfl
  rw [he,predecessor_anchor (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)]
  unfold leftIndex
  rw [translated_at_index]
  exact leftNeighbor_occurs (show 0<a by omega) hB hs

theorem original_disjoint {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (t w : Fin (cycleLength a B s)) :
    ¬SameEdge (C (by omega) (by omega) (by omega) t,
      C (by omega) (by omega) (by omega) (successor (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega))) t))
      (translatedExpandedCycle (by omega) (by omega) (by omega) w,
       translatedExpandedCycle (by omega) (by omega) (by omega)
        (successor (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega))) w)) := by
  have h := coordinatePair_disjoint ha hB heven hs (expandedCoordinates (show 0<B by omega) t)
    (expandedCoordinates (show 0<B by omega) w)
  simpa only [C,expandedCycle,translatedExpandedCycle,
    expandedCoordinates_next (show 0<a by omega) (show 0<B by omega) t,
    expandedCoordinates_next (show 0<a by omega) (show 0<B by omega) w] using h

def normalizedFork {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s) :
    ForkPair (FineVertex a B s) (cycleLength a B s) where
  large := length_large ha hB hs
  C := C (by omega) (by omega) (by omega)
  D := D (by omega) (by omega) (by omega)
  C_injective := expandedCycle_injective _ _ _
  D_injective := by
    intro i j h
    apply backward_injective (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega)))
      (anchorIndex (show 0<a by omega) (show 0<B by omega))
    exact translatedExpandedCycle_injective _ _ _ h
  anchor := by rw [C_zero (show 0<a by omega) hB (show 0<s by omega),D_zero (show 0<a by omega) hB (show 0<s by omega)]
  D_outside := by
    intro i he
    rw [D_first ha hB hs] at he
    exact leftNeighbor_exclusive (show 0<a by omega) (show 0<B by omega) hs
      (expandedCoordinates (show 0<B by omega) i) he.symm
  C_outside := by
    intro i he
    rw [C_first ha hB hs] at he
    exact rightNeighbor_exclusive (show 0<a by omega) (show 0<B by omega) hs
      (expandedCoordinates (show 0<B by omega)
        (backward (Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega)))
          (anchorIndex (show 0<a by omega) (show 0<B by omega)) i)) he.symm
  disjoint := by
    intro i j h
    let hL : 0<cycleLength a B s := Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega))
    let ai := anchorIndex (s := s) (show 0<a by omega) (show 0<B by omega)
    let t := backward hL ai (successor hL j)
    have ht : successor hL t=backward hL ai j := backward_successor hL ai j
    have he : SameEdge
        (D (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) j,
         D (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) (successor hL j))
        (translatedExpandedCycle (by omega) (by omega) (by omega) t,
         translatedExpandedCycle (by omega) (by omega) (by omega) (successor hL t)) := Or.inr (by rw [ht]; rfl)
    exact original_disjoint ha hB heven hs i t (sameEdge_trans h he)

#print axioms normalizedFork

theorem fineAdjacent_symm {a B s : Nat} (ha : 0<a) (hB : 0<B) (hs : 0<s)
    {u v : FineVertex a B s} (h : FineAdjacent ha hB hs u v) : FineAdjacent ha hB hs v u := by
  rcases h with h | h | ⟨hu,hv,hx,hy|hy⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hv,hu,hx.symm,Or.inr hy⟩)
  · exact Or.inr (Or.inr ⟨hv,hu,hx.symm,Or.inl hy⟩)

theorem normalized_union_in_host {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    {u v : FineVertex a B s} (h : (normalizedFork ha hB heven hs).unionRelation u v) :
    FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) u v := by
  apply (normalizedFork ha hB heven hs).union_in_host
    (fun _ _ h => fineAdjacent_symm _ _ _ h) ?_ ?_ h
  · intro i
    exact expandedCycle_adjacent ha hB heven (by omega) i
  · intro j
    let hL : 0<cycleLength a B s := Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega))
    let ai := anchorIndex (s := s) (show 0<a by omega) (show 0<B by omega)
    have hh := translatedExpandedCycle_adjacent ha hB heven (show 0<s by omega)
      (backward hL ai (successor hL j))
    rw [backward_successor] at hh
    exact fineAdjacent_symm _ _ _ hh

theorem normalized_union_covers_host {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    {u v : FineVertex a B s}
    (h : FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) u v) :
    (normalizedFork ha hB heven hs).unionRelation u v := by
  obtain ⟨c,p,hp⟩ := coordinatePair_cover ha hB heven (show 0<s by omega) u v h
  let hL : 0<cycleLength a B s := Nat.mul_pos (show 0<a by omega) (Nat.mul_pos (show 0<B by omega) (by omega))
  let t : Fin (cycleLength a B s) := expandedIndex p
  cases c
  · refine ⟨Sum.inl t,?_⟩
    change SameEdge (C (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) t,
      C (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) (successor hL t)) (u,v)
    unfold C expandedCycle
    rw [expandedCoordinates_next (show 0<a by omega) (show 0<B by omega)]
    simp only [t,expandedIndex_inverse]
    exact hp
  · let ai := anchorIndex (s := s) (show 0<a by omega) (show 0<B by omega)
    let j := backward hL ai (successor hL t)
    have hj : backward hL ai j=successor hL t := backward_inverse hL ai (successor hL t)
    have hjnext : backward hL ai (successor hL j)=t := by
      have he := backward_successor hL ai j
      rw [hj] at he
      have hh := congrArg (predecessor hL) he
      simpa only [predecessor_successor] using hh
    have hpt : SameEdge
        (translatedExpandedCycle (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) t,
         translatedExpandedCycle (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) (successor hL t)) (u,v) := by
      unfold translatedExpandedCycle
      rw [expandedCoordinates_next (show 0<a by omega) (show 0<B by omega)]
      simp only [t,expandedIndex_inverse]
      exact hp
    refine ⟨Sum.inr j,?_⟩
    change SameEdge (D (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) j,
      D (show 0<a by omega) (show 0<B by omega) (show 0<s by omega) (successor hL j)) (u,v)
    unfold D
    rw [hj,hjnext]
    exact sameEdge_trans (Or.inr rfl) hpt

/-- Unconditional actual two-path decomposition of the uniformly subdivided
anchored torus, with each path having aB(s+1)=AB(s+1)/2 edges. -/
def finePathDecomposition {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s) :
    GraphPathDecomposition (FineVertex a B s)
      (FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)) (cycleLength a B s) :=
  let d := (normalizedFork ha hB heven hs).decomposition
  { Index := d.Index
    indices := d.indices
    vertices := d.vertices
    simple := d.simple
    adjacent := fun p hp i => normalized_union_in_host ha hB heven hs (d.adjacent p hp i)
    cover := fun u v h => d.cover u v (normalized_union_covers_host ha hB heven hs h)
    unique := d.unique }

theorem finePathDecomposition_indices {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s) :
    (finePathDecomposition ha hB heven hs).indices=[false,true] := rfl

theorem finePath_length (a B s : Nat) : cycleLength a B s=(2*a)*B*(s+1)/2 := by
  have hc := uniform_subdivision_count a B s
  rw [←hc]
  simp only [cycleLength,Nat.mul_add,Nat.mul_one,Nat.mul_assoc]

/-- The same unconditional partition with the requested closed length formula. -/
def finePathDecompositionExact {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s) :
    GraphPathDecomposition (FineVertex a B s)
      (FineAdjacent (show 0<a by omega) (show 0<B by omega) (show 0<s by omega)) ((2*a)*B*(s+1)/2) := by
  rw [←finePath_length a B s]
  exact finePathDecomposition ha hB heven hs

theorem finePath_lists_nodup {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (p : Bool) : (List.ofFn ((finePathDecomposition ha hB heven hs).vertices p)).Nodup :=
  (normalizedFork ha hB heven hs).paths_nodup p

theorem finePath_lists_length {a B s : Nat} (ha : 2≤a) (hB : 4≤B) (heven : B%2=0) (hs : 2≤s)
    (p : Bool) : (List.ofFn ((finePathDecomposition ha hB heven hs).vertices p)).length=
      (2*a)*B*(s+1)/2+1 := by
  rw [List.length_ofFn,finePath_length]

#print axioms finePathDecompositionExact
#print axioms finePath_lists_nodup
#print axioms normalized_union_covers_host
#print axioms finePathDecomposition
end ErdePaths.ForkWiggle
