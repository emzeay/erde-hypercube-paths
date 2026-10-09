import ErdePaths.AACFine

namespace ErdePaths.AACFineClock
open SquareLift AACTransition AACMerge AACOwnership AACFine

private theorem block_telescoping {X : Type} (f : X→X) {w : Nat} (hw : 0<w)
    (b : Fin w→X) (z : X)
    (hs : ∀k, f (b k)=if h : k.val+1<w then b ⟨k.val+1,h⟩ else z) :
    b ⟨0,hw⟩ :: (List.ofFn b).map f=(List.ofFn b)++[z] := by
  cases w with
  | zero => omega
  | succ w =>
    rw [List.map_ofFn,List.ofFn_succ_last]
    have hi : (List.ofFn (fun i : Fin w => f (b i.castSucc)))=
        List.ofFn (fun i : Fin w => b i.succ) := by
      congr 1
      funext i
      rw [hs]
      simp only [Fin.val_castSucc]
      rw [dite_eq_left (show i.val+1<w+1 by have := i.isLt; omega)]
      rfl
    have hl : f (b (Fin.last w))=z := by rw [hs]; simp
    change b ⟨0,hw⟩ :: ((List.ofFn (fun i : Fin w => f (b i.castSucc)))++[f (b (Fin.last w))])=_
    rw [hi,hl,List.ofFn_succ]
    rfl

/-- Algebraic telescoping of consecutive variable-length blocks. The local
successor law is used at every offset; enumeration order is not assumed. -/
private theorem blocks_telescoping {X : Type} (f : X→X) : ∀n (b : Fin n→List X)
    (h : Fin (n+1)→X),
    (∀r, h r.castSucc :: (b r).map f=(b r)++[h r.succ]) →
    h 0 :: ((List.ofFn b).flatten).map f=(List.ofFn b).flatten++[h (Fin.last n)] := by
  intro n
  induction n with
  | zero => intro b h hs; simp
  | succ n ih =>
    intro b h hs
    let b' : Fin n→List X := fun r => b r.succ
    let h' : Fin (n+1)→X := fun r => h r.succ
    have hs' (r : Fin n) : h' r.castSucc :: (b' r).map f=(b' r)++[h' r.succ] := by
      simpa only [b',h',Fin.succ_castSucc] using hs r.succ
    have hi := ih b' h' hs'
    have h0 := hs (0 : Fin (n+1))
    have hz : (0 : Fin (n+1)).castSucc=(0 : Fin (n+1+1)) := Fin.ext rfl
    rw [hz] at h0
    rw [List.ofFn_succ,List.flatten_cons,List.map_append]
    change h 0 :: ((b 0).map f ++ ((List.ofFn b').flatten).map f)=
      (b 0 ++ (List.ofFn b').flatten)++[h (Fin.last (n+1))]
    rw [←List.cons_append,h0,List.append_assoc]
    change b 0 ++ (h' 0 :: ((List.ofFn b').flatten).map f)=_
    rw [hi,List.append_assoc]
    rfl


private def headAt {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (n : Nat) : ExpandedIndex (A := A) C :=
  ⟨⟨n%N,Nat.mod_lt _ hN⟩,⟨0,weight_pos hA _⟩⟩

private theorem headAt_row {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) (r : Fin N) :
    headAt hA C r.val=⟨r,⟨0,weight_pos hA _⟩⟩ := by
  have he : (⟨r.val%N,Nat.mod_lt _ hN⟩ : Fin N)=r := Fin.ext (Nat.mod_eq_of_lt r.isLt)
  exact congrArg (fun r : Fin N => (⟨r,⟨0,weight_pos hA _⟩⟩ : ExpandedIndex (A := A) C)) he

private theorem indexList_form {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    indexList (A := A) C=(List.ofFn (fun r : Fin N => List.ofFn
      (fun k : Fin (weight A (atPair turns (C.point r)).2.2) => (⟨r,k⟩ : ExpandedIndex C)))).flatten := by
  simp only [indexList,List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]

theorem indexList_telescoping {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    headAt hA C 0 :: (indexList C).map (expandedNext hA C)=(indexList C)++[headAt hA C 0] := by
  let b (r : Fin N) := List.ofFn (fun k : Fin (weight A (atPair turns (C.point r)).2.2) =>
    (⟨r,k⟩ : ExpandedIndex (A := A) C))
  let h (r : Fin (N+1)) := headAt hA C r.val
  have hs (r : Fin N) : h r.castSucc :: (b r).map (expandedNext hA C)=(b r)++[h r.succ] := by
    have hl := block_telescoping (expandedNext hA C) (weight_pos hA (atPair turns (C.point r)).2.2)
      (fun k => (⟨r,k⟩ : ExpandedIndex (A := A) C)) (headAt hA C (r.val+1))
      (fun k => by
        unfold expandedNext
        split
        · rfl
        · rfl)
    change headAt hA C r.val :: _ = _
    rw [headAt_row]
    exact hl
  have hl := blocks_telescoping (expandedNext hA C) N b h hs
  change headAt hA C 0 :: ((List.ofFn b).flatten).map (expandedNext hA C)=
    (List.ofFn b).flatten++[headAt hA C N] at hl
  rw [←indexList_form C] at hl
  have he : headAt hA C N=headAt hA C 0 := by
    apply congrArg (fun r : Fin N => (⟨r,⟨0,weight_pos hA _⟩⟩ : ExpandedIndex (A := A) C))
    apply Fin.ext
    simp
  rw [he] at hl
  exact hl

theorem indexList_rotation {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    (indexList C).map (expandedNext hA C)=(indexList C).tail++[headAt hA C 0] := by
  have hl := indexList_telescoping hA C
  have hm := indexList_mem C (headAt hA C 0)
  cases hx : indexList (A := A) C with
  | nil => simp [hx] at hm
  | cons x xs =>
    rw [hx] at hl
    simp only [List.cons_append,List.cons.injEq] at hl
    exact hl.2

private theorem indexList_head {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    (indexList C)[0]?=some (headAt hA C 0) := by
  have hl := indexList_telescoping hA C
  have hm := indexList_mem C (headAt hA C 0)
  cases hx : indexList (A := A) C with
  | nil => simp [hx] at hm
  | cons x xs =>
    rw [hx] at hl
    simp only [List.cons_append,List.cons.injEq] at hl
    exact congrArg some hl.1.symm


private theorem list_successor {X : Type} (l : List X) (hL : 0<l.length)
    (f : X→X) (z : X) (hr : l.map f=l.tail++[z]) (hh : l[0]?=some z)
    (n : Fin l.length) : f l[n.val]=l[(successor hL n).val] := by
  have he := congrArg (fun xs : List X => xs[n.val]?) hr
  rw [List.getElem?_map,List.getElem?_append,List.getElem?_eq_getElem n.isLt] at he
  by_cases hn : n.val+1<l.length
  · have hb : n.val<l.tail.length := by simp only [List.length_tail]; omega
    rw [ite_eq_left hb,List.getElem?_tail,List.getElem?_eq_getElem hn] at he
    have hs : (successor hL n).val=n.val+1 := Nat.mod_eq_of_lt hn
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem (successor hL n).isLt,hs]
    rw [List.getElem?_eq_getElem hn]
    exact he
  · have hn' : n.val+1=l.length := by have := n.isLt; omega
    have hb : ¬n.val<l.tail.length := by simp only [List.length_tail]; omega
    have hz : n.val-l.tail.length=0 := by simp only [List.length_tail]; omega
    rw [ite_eq_right hb,hz] at he
    simp only [Option.map_some,List.getElem?_cons_zero] at he
    have hs : (successor hL n).val=0 := by simp [successor,hn']
    apply Option.some.inj
    rw [←List.getElem?_eq_getElem (successor hL n).isLt,hs]
    exact he.trans hh.symm

def numericPosition {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (n : Fin (indexList (A := A) C).length) : ExpandedIndex (A := A) C :=
  (indexList C)[n.val]

theorem numericPosition_injective {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    Function.Injective (numericPosition (A := A) C) := by
  intro n m he
  apply Fin.ext
  exact (List.nodup_iff_eq_of_getElem_eq.mp (indexList_nodup C)) n.val m.val n.isLt m.isLt he

theorem numericPosition_surjective {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    Function.Surjective (numericPosition (A := A) C) := by
  intro p
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp (indexList_mem C p)
  exact ⟨⟨n,hn⟩,he⟩

theorem numericPosition_next {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (n : Fin (indexList (A := A) C).length) :
    expandedNext hA C (numericPosition C n)=numericPosition C
      (successor (List.length_pos_of_mem (indexList_mem C (headAt hA C 0))) n) :=
  list_successor (indexList C) _ (expandedNext hA C) (headAt hA C 0)
    (indexList_rotation hA C) (indexList_head hA C) n

noncomputable def numericInverse {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : Fin (indexList (A := A) C).length :=
  Classical.choose (numericPosition_surjective C p)

theorem numericPosition_inverse {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : numericPosition C (numericInverse C p)=p :=
  Classical.choose_spec (numericPosition_surjective C p)

theorem numericInverse_position {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (n : Fin (indexList (A := A) C).length) : numericInverse C (numericPosition C n)=n :=
  numericPosition_injective C (numericPosition_inverse C _)


/-- Numeric fine position on any proved exact length, retaining the literal
lexicographic enumeration order. -/
def exactPosition {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (n : Fin E) : ExpandedIndex (A := A) C :=
  numericPosition C (Fin.cast hE.symm n)

theorem exactPosition_injective {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) : Function.Injective (exactPosition C hE) := by
  intro n m he
  have hh := numericPosition_injective C he
  exact Fin.ext (congrArg (fun i : Fin (indexList (A := A) C).length => i.val) hh)

theorem exactPosition_surjective {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) : Function.Surjective (exactPosition C hE) := by
  intro p
  obtain ⟨n,hn⟩ := numericPosition_surjective C p
  refine ⟨Fin.cast hE n,?_⟩
  have he : Fin.cast hE.symm (Fin.cast hE n)=n := Fin.ext rfl
  simpa only [exactPosition,he] using hn

theorem exactPosition_next {K A B N E : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (n : Fin E) :
    expandedNext hA C (exactPosition C hE n)=exactPosition C hE (successor hpos n) := by
  unfold exactPosition
  rw [numericPosition_next]
  congr 1
  apply Fin.ext
  change (n.val+1)%(indexList C).length=(n.val+1)%E
  rw [hE]

noncomputable def exactInverse {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (p : ExpandedIndex (A := A) C) : Fin E :=
  Fin.cast hE (numericInverse C p)

theorem exactPosition_inverse {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (p : ExpandedIndex (A := A) C) :
    exactPosition C hE (exactInverse C hE p)=p := by
  have he : Fin.cast hE.symm (Fin.cast hE (numericInverse C p))=numericInverse C p := Fin.ext rfl
  simpa only [exactPosition,exactInverse,he] using numericPosition_inverse C p

theorem exactInverse_position {K A B N E : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (n : Fin E) :
    exactInverse C hE (exactPosition C hE n)=n :=
  exactPosition_injective C hE (exactPosition_inverse C hE _)

def fineVertex {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (n : Fin E) : Fine K A B :=
  expandedVertex hK hA hB C (exactPosition C hE n)

def fineLabel {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (n : Fin E) : FineEdge K A B :=
  expandedLabel hK hA hB C (exactPosition C hE n)

theorem fineVertex_step {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (n : Fin E) :
    SameEdge (AACTransition.decode hK hA hB (fineLabel hK hA hB C hE n))
      (fineVertex hK hA hB C hE n,fineVertex hK hA hB C hE (successor hpos n)) := by
  have hs := expanded_step hK hA hB C (exactPosition C hE n)
  rw [exactPosition_next hA C hE hpos n] at hs
  exact hs

/-- Exact numeric fine Euler clock, constructed without an Euler/traversal
existence premise. The clock has repeated grid vertices and unique edges. -/
theorem numeric_fine_euler {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (AACInduction.turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
    ∃hE : (indexList (A := A) C).length=K*B*(A+1),
      (Function.Injective (fineLabel hK hA hB C hE) ∧ Function.Surjective (fineLabel hK hA hB C hE)) ∧
      (∀n, SameEdge (AACTransition.decode hK hA hB (fineLabel hK hA hB C hE n))
        (fineVertex hK hA hB C hE n,fineVertex hK hA hB C hE
          (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n))) := by
  obtain ⟨C,⟨hinj,hsur⟩,hstep⟩ := fine_expansion_indexed hK hA hB t hb ht
  let hE := indexList_length hK hA hB C hinj hsur
  refine ⟨C,hE,⟨?_,?_⟩,fineVertex_step hK hA hB C hE _⟩
  · intro n m he
    exact exactPosition_injective C hE (hinj he)
  · intro e
    obtain ⟨p,hp⟩ := hsur e
    obtain ⟨n,hn⟩ := exactPosition_surjective C hE p
    exact ⟨n,by change expandedLabel hK hA hB C (exactPosition C hE n)=e; rw [hn,hp]⟩


theorem numeric_physical_unique {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE)) (n m : Fin E)
    (he : SameEdge (fineVertex hK hA hB C hE n,fineVertex hK hA hB C hE (successor hpos n))
      (fineVertex hK hA hB C hE m,fineVertex hK hA hB C hE (successor hpos m))) : n=m := by
  apply hinj
  apply fine_decode_unique hK hA hB h3 hB3
  exact sameEdge_trans (fineVertex_step hK hA hB C hE hpos n)
    (sameEdge_trans he (sameEdge_symm (fineVertex_step hK hA hB C hE hpos m)))

/-- Actual fine graph edge cover and unique numeric occurrence, retaining
repeated grid vertices and the checked cyclic last-to-first edge. -/
theorem physical_fine_euler {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (AACInduction.turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
    ∃hE : (indexList (A := A) C).length=K*B*(A+1),
      (∀n, AACTransition.Adjacent hK hA hB (fineVertex hK hA hB C hE n)
        (fineVertex hK hA hB C hE (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n))) ∧
      (∀u v, AACTransition.Adjacent hK hA hB u v →
        ∃n : Fin (K*B*(A+1)),
          SameEdge (fineVertex hK hA hB C hE n,
            fineVertex hK hA hB C hE (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) n)) (u,v) ∧
          (∀m, SameEdge (fineVertex hK hA hB C hE m,
            fineVertex hK hA hB C hE (successor (Nat.mul_pos (Nat.mul_pos hK hB) (by omega)) m)) (u,v) → m=n)) := by
  obtain ⟨C,hE,⟨hinj,hsur⟩,hstep⟩ := numeric_fine_euler hK hA hB t hb ht
  let hpos : 0<K*B*(A+1) := Nat.mul_pos (Nat.mul_pos hK hB) (by omega)
  refine ⟨C,hE,?_,?_⟩
  · intro n
    exact ⟨fineLabel hK hA hB C hE n,hstep n⟩
  · intro u v huv
    obtain ⟨e,he⟩ := huv
    obtain ⟨n,hn⟩ := hsur e
    have hcover : SameEdge (fineVertex hK hA hB C hE n,
        fineVertex hK hA hB C hE (successor hpos n)) (u,v) := by
      have hs := hstep n
      change SameEdge (AACTransition.decode hK hA hB (fineLabel hK hA hB C hE n)) _ at hs
      rw [hn] at hs
      exact sameEdge_trans (sameEdge_symm hs) he
    refine ⟨n,hcover,?_⟩
    intro m hm
    exact numeric_physical_unique hK hA hB h3 hB3 C hE hpos hinj m n
      (sameEdge_trans hm (sameEdge_symm hcover))

#print axioms indexList_rotation
#print axioms numericPosition_next
#print axioms exactPosition_inverse
#print axioms exactInverse_position
#print axioms numeric_fine_euler
#print axioms physical_fine_euler

end ErdePaths.AACFineClock
