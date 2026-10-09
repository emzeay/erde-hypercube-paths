import ErdePaths.AACOwnership

namespace ErdePaths.AACFine
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open SquareLift AACTransition AACMerge AACOwnership AnchoredEmbedding

/-- Fine length of an actual outgoing coarse port. -/
def weight (A : Nat) : Port→Nat
  | .up | .down => A
  | .right | .left => 1

theorem weight_pos (hA : 0<A) (p : Port) : 0<weight A p := by cases p <;> simp [weight,hA]

/-- Literal fine vertices on a directed coarse-edge subdivision, including
both endpoint grids. No output path is supplied as a hypothesis. -/
def segment {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (k : Fin (weight A s.2.2+1)) : Fine K A B :=
  match p : s.2.2 with
  | .up => if hk : k.val<A then (positionEncode s.1 ⟨k.val,hk⟩,s.2.1)
      else gridPoint hA (successor hK s.1,s.2.1)
  | .down => if hk : k.val=0 then gridPoint hA (s.1,s.2.1)
      else (positionEncode (predecessor hK s.1) ⟨A-k.val,by
        have hh : k.val<A+1 := by simpa only [p,weight] using k.isLt
        omega⟩,s.2.1)
  | .right => if k.val=0 then gridPoint hA (s.1,s.2.1)
      else gridPoint hA (s.1,successor hB s.2.1)
  | .left => if k.val=0 then gridPoint hA (s.1,s.2.1)
      else gridPoint hA (s.1,predecessor hB s.2.1)

/-- The actual fine positive-edge label, even for a reversed traversal. -/
def segmentLabel {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (k : Fin (weight A s.2.2)) : FineEdge K A B :=
  match p : s.2.2 with
  | .up => .inl (positionEncode s.1 ⟨k.val,by simpa only [p,weight] using k.isLt⟩,s.2.1)
  | .down => .inl (positionEncode (predecessor hK s.1) ⟨A-1-k.val,by
      have hh : k.val<A := by simpa only [p,weight] using k.isLt
      omega⟩,s.2.1)
  | .right => .inr (s.1,s.2.1)
  | .left => .inr (s.1,predecessor hB s.2.1)

theorem segment_start {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) (s : State K B) :
    segment hK hA hB s ⟨0,by have := weight_pos hA s.2.2; omega⟩=
      gridPoint hA (stateVertex s) := by
  rcases s with ⟨i,j,p⟩
  cases p <;> simp [segment,gridPoint,stateVertex,hA]

theorem segment_end {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) (s : State K B) :
    segment hK hA hB s ⟨weight A s.2.2,by omega⟩=
      gridPoint hA (stateVertex (cross hK hB s)) := by
  rcases s with ⟨i,j,p⟩
  cases p <;> simp [segment,weight,gridPoint,stateVertex,cross,Nat.ne_of_gt hA]

private theorem encode_successor {K A : Nat} (hK : 0<K) (hA : 0<A)
    (i : Fin K) (a : Fin A) :
    successor (Nat.mul_pos hK hA) (positionEncode i a)=
      if ha : a.val+1<A then positionEncode i ⟨a.val+1,ha⟩
      else positionEncode (successor hK i) ⟨0,hA⟩ := by
  apply Fin.ext
  by_cases ha : a.val+1<A
  · simp only [ha,↓reduceDIte,positionEncode,successor]
    exact Nat.mod_eq_of_lt (by
      have hi := Nat.mul_le_mul_left A (show i.val+1≤K by have := i.isLt; omega)
      simp only [Nat.mul_add,Nat.mul_one] at hi
      rw [Nat.mul_comm K A]
      
      omega)
  · have he : a.val+1=A := by have := a.isLt; omega
    simp only [ha,↓reduceDIte,positionEncode,successor]
    have hs : A*i.val+a.val+1=A*(i.val+1) := by
      simp only [Nat.mul_add,Nat.mul_one]
      omega
    rw [hs]
    by_cases hi : i.val+1<K
    · rw [Nat.mod_eq_of_lt hi]
      have hl : A*(i.val+1)<K*A := by
        have := Nat.mul_lt_mul_of_pos_left hi hA
        simpa only [Nat.mul_comm] using this
      rw [Nat.mod_eq_of_lt hl]
      omega
    · have hi' : i.val+1=K := by have := i.isLt; omega
      rw [hi',Nat.mod_self]
      simp [Nat.mul_comm]

/-- Every local fine step decodes to its literal consecutive vertices. -/
theorem segment_step {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (k : Fin (weight A s.2.2)) :
    SameEdge (AACTransition.decode hK hA hB (segmentLabel hK hA hB s k))
      (segment hK hA hB s k.castSucc,segment hK hA hB s k.succ) := by
  rcases s with ⟨i,j,p⟩
  cases p
  · change Fin A at k
    apply Or.inl
    have hk : k.val<A := k.isLt
    simp only [segmentLabel,segment,AACTransition.decode,weight,hk,↓reduceDIte,Fin.val_castSucc,Fin.val_succ]
    rw [encode_successor hK hA]
    split <;> simp [gridPoint,positionEncode]
  · change Fin 1 at k
    have hk : k.val=0 := by have := k.isLt; change k.val<1 at this; omega
    apply Or.inl
    simp [segmentLabel,segment,AACTransition.decode,weight,hk]
  · change Fin A at k
    apply Or.inr
    have hk : k.val<A := k.isLt
    have hr : A-1-k.val+1=A-k.val := by omega
    simp only [segmentLabel,AACTransition.decode]
    rw [encode_successor hK hA]
    by_cases hz : k.val=0
    · have he : ¬A-1-k.val+1<A := by omega
      simp [segment,weight,hz,show ¬A-1+1<A by omega,gridPoint,successor_predecessor]
    · have he : A-1-k.val+1<A := by omega
      have hn : k.val+1≠0 := by omega
      simp [segment,weight,hz,hn,he,hr,gridPoint]
      simp [Nat.sub_sub,Nat.add_comm,show A-k.val<A by omega]
  · change Fin 1 at k
    have hk : k.val=0 := by have := k.isLt; change k.val<1 at this; omega
    apply Or.inr
    simp [segmentLabel,segment,AACTransition.decode,weight,hk,successor_predecessor]


/-- Source coarse-edge label of a literal fine subdivision label. -/
def project {K A B : Nat} (hA : 0<A) : FineEdge K A B→CoarseEdge K B
  | .inl (x,j) => .inl ((positionDecode hA x).1,j)
  | .inr v => .inr v

theorem segment_project {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (k : Fin (weight A s.2.2)) :
    project hA (segmentLabel hK hA hB s k)=AACEdge.incoming hK hB (cross hK hB s) := by
  rcases s with ⟨i,j,p⟩
  cases p <;> simp [segmentLabel,project,positionDecode_encode,AACEdge.incoming,cross,predecessor_successor]

theorem segment_label_injective {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) : Function.Injective (segmentLabel hK hA hB s) := by
  rcases s with ⟨i,j,p⟩
  intro k l he
  cases p
  · change Fin A at k l
    have hx : positionEncode i k=positionEncode i l := congrArg Prod.fst (Sum.inl.inj he)
    have hh := positionEncode_injective hA (a₁ := (i,k)) (a₂ := (i,l)) hx
    exact congrArg Prod.snd hh
  · change Fin 1 at k l
    apply Fin.ext
    have := k.isLt; have := l.isLt; omega
  · change Fin A at k l
    have hx := congrArg (fun e : FineEdge K A B => match e with
      | .inl (x,_) => (positionDecode hA x).2.val
      | .inr _ => 0) he
    simp only [segmentLabel,positionDecode_encode] at hx
    apply Fin.ext
    have := k.isLt; have := l.isLt; omega
  · change Fin 1 at k l
    apply Fin.ext
    have := k.isLt; have := l.isLt; omega

theorem segment_label_covers {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (s : State K B) (e : FineEdge K A B)
    (he : project hA e=AACEdge.incoming hK hB (cross hK hB s)) :
    ∃k, segmentLabel hK hA hB s k=e := by
  rcases s with ⟨i,j,p⟩
  cases p <;> cases e
  all_goals simp only [project,AACEdge.incoming,cross,predecessor_successor,
    Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq,Prod.mk.injEq] at he
  all_goals try contradiction
  case up.inl e =>
    rcases e with ⟨x,j'⟩
    rcases he with ⟨hi,hj⟩
    change j'=j at hj
    subst j'
    refine ⟨(positionDecode hA x).2,?_⟩
    change Sum.inl (positionEncode i (positionDecode hA x).2,j)=Sum.inl (x,j)
    rw [←hi,positionEncode_decode]
  case down.inl e =>
    rcases e with ⟨x,j'⟩
    rcases he with ⟨hi,hj⟩
    change j'=j at hj
    subst j'
    let a := (positionDecode hA x).2
    have ha : A-1-a.val<A := by have := a.isLt; omega
    refine ⟨⟨A-1-a.val,ha⟩,?_⟩
    have hh : A-1-(A-1-a.val)=a.val := by have := a.isLt; omega
    change Sum.inl (positionEncode (predecessor hK i) ⟨A-1-(A-1-a.val),_⟩,j)=Sum.inl (x,j)
    have hk : (⟨A-1-(A-1-a.val),by rw [hh]; exact a.isLt⟩ : Fin A)=a := Fin.ext hh
    rw [hk,←hi]
    exact congrArg (fun x => Sum.inl (x,j)) (positionEncode_decode hA x)
  case right.inr e =>
    change e=(i,j) at he
    subst e
    exact ⟨⟨0,by simp [weight]⟩,rfl⟩
  case left.inr e =>
    change e=(i,predecessor hB j) at he
    subst e
    exact ⟨⟨0,by simp [weight]⟩,rfl⟩

/-- Expansion positions retain actual coarse order and local directed offsets. -/
abbrev ExpandedIndex {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :=
  (r : Fin N) × Fin (weight A (atPair turns (C.point r)).2.2)

def expandedVertex {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : Fine K A B :=
  segment hK hA hB (atPair turns (C.point p.1)) p.2.castSucc

def expandedLabel {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : FineEdge K A B :=
  segmentLabel hK hA hB (atPair turns (C.point p.1)) p.2

def expandedNext {K A B N : Nat} (hA : 0<A) {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : ExpandedIndex (A := A) C :=
  if hk : p.2.val+1<weight A (atPair turns (C.point p.1)).2.2 then
    ⟨p.1,⟨p.2.val+1,hk⟩⟩
  else ⟨successor hN p.1,⟨0,weight_pos hA _⟩⟩

/-- Successive segment endpoints coincide, including the coarse cyclic seam. -/
theorem segment_seam {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (r : Fin N) :
    segment hK hA hB (atPair turns (C.point r)) ⟨weight A (atPair turns (C.point r)).2.2,by omega⟩=
      segment hK hA hB (atPair turns (C.point (successor hN r))) ⟨0,by have := weight_pos hA (atPair turns (C.point (successor hN r))).2.2; omega⟩ := by
  rw [segment_end,segment_start,←C.next r]
  rfl

/-- Literal adjacency for the actual lexicographic cyclic expanded traversal. -/
theorem expanded_step {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) :
    SameEdge (AACTransition.decode hK hA hB (expandedLabel hK hA hB C p))
      (expandedVertex hK hA hB C p,expandedVertex hK hA hB C (expandedNext hA C p)) := by
  have hs := segment_step hK hA hB (atPair turns (C.point p.1)) p.2
  change SameEdge _ (segment hK hA hB _ p.2.castSucc,_)
  by_cases hk : p.2.val+1<weight A (atPair turns (C.point p.1)).2.2
  · have he : (⟨p.2.val+1,hk⟩ : Fin (weight A (atPair turns (C.point p.1)).2.2)).castSucc=p.2.succ := Fin.ext rfl
    unfold expandedNext
    rw [dite_eq_left hk]
    change SameEdge _ (segment hK hA hB _ p.2.castSucc,
      segment hK hA hB _ (⟨p.2.val+1,hk⟩ : Fin (weight A (atPair turns (C.point p.1)).2.2)).castSucc)
    rw [he]
    exact hs
  · have he : p.2.succ=⟨weight A (atPair turns (C.point p.1)).2.2,by omega⟩ := by
      apply Fin.ext
      have := p.2.isLt
      change p.2.val+1=weight A (atPair turns (C.point p.1)).2.2
      omega
    rw [he,segment_seam hK hA hB C p.1] at hs
    unfold expandedNext
    rw [dite_eq_right hk]
    exact hs


theorem expanded_project {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) :
    project hA (expandedLabel hK hA hB C p)=AACEdge.incoming hK hB (C.point (successor hN p.1)) := by
  rw [expandedLabel,segment_project]
  change AACEdge.incoming hK hB (transition hK hB turns (C.point p.1))=_
  rw [C.next]

theorem expanded_label_injective {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hinj : Function.Injective (fun r => AACEdge.incoming hK hB (C.point (successor hN r)))) :
    Function.Injective (expandedLabel hK hA hB C) := by
  rintro ⟨r,k⟩ ⟨q,l⟩ he
  have hp := congrArg (project hA) he
  rw [expanded_project,expanded_project] at hp
  have hr : r=q := hinj hp
  subst q
  have hk := segment_label_injective hK hA hB (atPair turns (C.point r)) he
  change k=l at hk
  subst l
  rfl

theorem expanded_label_surjective {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hsur : Function.Surjective (fun r => AACEdge.incoming hK hB (C.point (successor hN r)))) :
    Function.Surjective (expandedLabel hK hA hB C) := by
  intro e
  obtain ⟨r,hr⟩ := hsur (project hA e)
  have he : project hA e=AACEdge.incoming hK hB (cross hK hB (atPair turns (C.point r))) := by
    change project hA e=AACEdge.incoming hK hB (transition hK hB turns (C.point r))
    rw [C.next]
    exact hr.symm
  obtain ⟨k,hk⟩ := segment_label_covers hK hA hB (atPair turns (C.point r)) e he
  exact ⟨⟨r,k⟩,hk⟩

/-- Unconditional actual ordered labelled subdivision of the constructed AAC.
The index is the finite lexicographic subdivision of the coarse cyclic clock. -/
theorem fine_expansion_indexed {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (AACInduction.turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
      (Function.Injective (expandedLabel hK hA hB C) ∧ Function.Surjective (expandedLabel hK hA hB C)) ∧
      (∀p, SameEdge (AACTransition.decode hK hA hB (expandedLabel hK hA hB C p))
        (expandedVertex hK hA hB C p,expandedVertex hK hA hB C (expandedNext hA C p))) := by
  obtain ⟨C,⟨hinj,hsur⟩,hstep⟩ := coarse_euler_steps hK hB t hb ht
  exact ⟨C,⟨expanded_label_injective hK hA hB C hinj,
    expanded_label_surjective hK hA hB C hsur⟩,expanded_step hK hA hB C⟩

/-- Fine physical endpoint pairs distinguish all labels under the genuine
cycle-size hypotheses; coarse K=2 remains allowed. -/
theorem fine_decode_unique {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (e f : FineEdge K A B)
    (he : SameEdge (AACTransition.decode hK hA hB e) (AACTransition.decode hK hA hB f)) : e=f := by
  have gridinj (u v : Grid K B) (h : gridPoint hA u=gridPoint hA v) : u=v := by
    have h1 := congrArg (fun x : Fine K A B => (positionDecode hA x.1).1) h
    have h2 := congrArg Prod.snd h
    simp only [gridPoint,positionDecode_encode] at h1
    exact Prod.ext h1 h2
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have h := Wiggle.axisEdge_unique h3 hB3 true true e f he
      exact congrArg Sum.inl h.2
    | inr f =>
      have h := Wiggle.axisEdge_unique h3 hB3 true false e (gridPoint hA f) he
      cases h.1
  | inr e =>
    cases f with
    | inl f =>
      have h := Wiggle.axisEdge_unique h3 hB3 false true (gridPoint hA e) f he
      cases h.1
    | inr f =>
      have h := Wiggle.axisEdge_unique h3 hB3 false false (gridPoint hA e) (gridPoint hA f) he
      exact congrArg Sum.inr (gridinj e f h.2)

private theorem ofFn_nodup {X : Type} {n : Nat} (f : Fin n→X) (hf : Function.Injective f) :
    (List.ofFn f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj he
  simp only [List.getElem_ofFn] at he
  exact congrArg Fin.val (hf he)

private theorem map_nodup {X Y : Type} (f : X→Y) (hf : Function.Injective f)
    (l : List X) (hl : l.Nodup) : (l.map f).Nodup := by
  exact List.Pairwise.map f (fun a b h he => h (hf he)) hl

/-- Concrete lexicographic list of every finite subdivision position. -/
def indexList {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    List (ExpandedIndex (A := A) C) :=
  (List.finRange N).flatMap (fun r => (List.finRange (weight A (atPair turns (C.point r)).2.2)).map
    (fun k => (⟨r,k⟩ : ExpandedIndex (A := A) C)))

theorem indexList_mem {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (p : ExpandedIndex (A := A) C) : p∈indexList C := by
  rcases p with ⟨r,k⟩
  exact List.mem_flatMap.mpr ⟨r,List.mem_finRange r,List.mem_map.mpr ⟨k,List.mem_finRange k,rfl⟩⟩

theorem indexList_nodup {K A B N : Nat} {hK : 0<K} {hB : 0<B} {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN) :
    (indexList (A := A) C).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro r hr
    apply map_nodup _ _ _ (List.nodup_finRange _)
    intro k l he
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
  · apply (List.nodup_finRange N).imp
    intro r q hne x hx y hy he
    obtain ⟨k,hk,hx⟩ := List.mem_map.mp hx
    obtain ⟨l,hl,hy⟩ := List.mem_map.mp hy
    apply hne
    exact congrArg Sigma.fst (hx.trans (he.trans hy.symm))

/-- Canonical fine-edge enumeration, with no cyclic parallel labels collapsed. -/
def fineLabels (K A B : Nat) (hB : 0<B) : List (FineEdge K A B) :=
  (List.ofFn (fun n : Fin ((K*A)*B) => Sum.inl (positionDecode hB n))) ++
  (List.ofFn (fun n : Fin (K*B) => Sum.inr (positionDecode hB n)))

theorem fineLabels_nodup (K A B : Nat) (hB : 0<B) : (fineLabels K A B hB).Nodup := by
  apply List.nodup_append.mpr
  constructor
  · apply ofFn_nodup
    intro i j he
    have hp := Sum.inl.inj he
    have hh := congrArg (fun p => positionEncode p.1 p.2) hp
    simpa only [positionEncode_decode] using hh
  constructor
  · apply ofFn_nodup
    intro i j he
    have hp := Sum.inr.inj he
    have hh := congrArg (fun p => positionEncode p.1 p.2) hp
    simpa only [positionEncode_decode] using hh
  · intro x hx y hy he
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hy
    have h := hi.trans (he.trans hj.symm)
    cases h

theorem fineLabels_mem {K A B : Nat} (hB : 0<B) (e : FineEdge K A B) : e∈fineLabels K A B hB := by
  cases e with
  | inl e => exact List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨positionEncode e.1 e.2,by simp [positionDecode_encode]⟩))
  | inr e => exact List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨positionEncode e.1 e.2,by simp [positionDecode_encode]⟩))

theorem fineLabels_length (K A B : Nat) (hB : 0<B) : (fineLabels K A B hB).length=K*B*(A+1) := by
  simp only [fineLabels,List.length_append,List.length_ofFn]
  simp only [Nat.mul_add,Nat.mul_one]
  rw [Nat.mul_right_comm K A B]

/-- Exact total expanded-edge count, derived from constructed label ownership. -/
theorem indexList_length {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) {hN : 0<N}
    {turns : Grid K B→Bool} (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hinj : Function.Injective (expandedLabel hK hA hB C))
    (hsur : Function.Surjective (expandedLabel hK hA hB C)) :
    (indexList (A := A) C).length=K*B*(A+1) := by
  have hn := map_nodup (expandedLabel hK hA hB C) hinj (indexList C) (indexList_nodup C)
  have hp : List.Perm ((indexList C).map (expandedLabel hK hA hB C)) (fineLabels K A B hB) := by
    apply (List.perm_ext_iff_of_nodup hn (fineLabels_nodup K A B hB)).mpr
    intro e
    constructor
    · intro he; exact fineLabels_mem hB e
    · intro he
      obtain ⟨p,hp⟩ := hsur e
      exact List.mem_map.mpr ⟨p,indexList_mem C p,hp⟩
  have hl := hp.length_eq
  rw [List.length_map,fineLabels_length] at hl
  exact hl

/-- Physical fine-step uniqueness follows from actual label ownership and
fine decode uniqueness, without a simplicity premise on fine vertices. -/
theorem expanded_physical_unique {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) {hN : 0<N} {turns : Grid K B→Bool}
    (C : Orbit (State K B) (transition hK hB turns) N hN)
    (hinj : Function.Injective (expandedLabel hK hA hB C))
    (p q : ExpandedIndex (A := A) C)
    (he : SameEdge (expandedVertex hK hA hB C p,expandedVertex hK hA hB C (expandedNext hA C p))
      (expandedVertex hK hA hB C q,expandedVertex hK hA hB C (expandedNext hA C q))) : p=q := by
  apply hinj
  apply fine_decode_unique hK hA hB h3 hB3
  exact sameEdge_trans (expanded_step hK hA hB C p)
    (sameEdge_trans he (sameEdge_symm (expanded_step hK hA hB C q)))

/-- Combined unconditional construction: literal indexed expansion, exact
fine-label ownership/count, and physical-step uniqueness for genuine cycles.
Numeric/list successor transport is deliberately not assumed here. -/
theorem constructed_fine {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (t : Fin K→Bool) (hb : BalancedTurns t) (ht : t ⟨0,hK⟩=false) :
    ∃C : Orbit (State K B) (transition hK hB (AACInduction.turnsAfter hK t (B-1)))
        (B*(2*K)) (Nat.mul_pos hB (by omega)),
      (Function.Injective (expandedLabel hK hA hB C) ∧ Function.Surjective (expandedLabel hK hA hB C)) ∧
      (indexList (A := A) C).length=K*B*(A+1) ∧
      (∀p, SameEdge (AACTransition.decode hK hA hB (expandedLabel hK hA hB C p))
        (expandedVertex hK hA hB C p,expandedVertex hK hA hB C (expandedNext hA C p))) ∧
      (∀p q, SameEdge (expandedVertex hK hA hB C p,expandedVertex hK hA hB C (expandedNext hA C p))
        (expandedVertex hK hA hB C q,expandedVertex hK hA hB C (expandedNext hA C q)) → p=q) := by
  obtain ⟨C,⟨hinj,hsur⟩,hstep⟩ := fine_expansion_indexed hK hA hB t hb ht
  exact ⟨C,⟨hinj,hsur⟩,indexList_length hK hA hB C hinj hsur,hstep,
    expanded_physical_unique hK hA hB h3 hB3 C hinj⟩

#print axioms segment_step
#print axioms expanded_step
#print axioms expanded_label_injective
#print axioms expanded_label_surjective
#print axioms fine_expansion_indexed
#print axioms fine_decode_unique
#print axioms indexList_length
#print axioms constructed_fine

end ErdePaths.AACFine
