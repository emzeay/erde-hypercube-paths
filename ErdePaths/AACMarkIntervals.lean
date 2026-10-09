import ErdePaths.AACFineGeometry
import ErdePaths.AACUnfold

namespace ErdePaths.AACMarkIntervals
open SquareLift AACTransition AACFine AACFineGeometry

/-- Physical endpoint color on the second-axis cycle. -/
def rowColor {B : Nat} (j : Fin B) : Bool := decide (j.val%2=1)

theorem rowColor_successor {B : Nat} (hB : 0<B) (hb : B%2=0) (j : Fin B) :
    rowColor (successor hB j)=!rowColor j := by
  apply Bool.eq_iff_iff.mpr
  simp only [rowColor,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
  change ((j.val+1)%B)%2=1 ↔ ¬j.val%2=1
  have hd : 2∣B := Nat.dvd_of_mod_eq_zero hb
  rw [Nat.mod_mod_of_dvd _ hd]
  omega

theorem rowColor_predecessor {B : Nat} (hB : 0<B) (hb : B%2=0) (j : Fin B) :
    rowColor (predecessor hB j)=!rowColor j := by
  have h := rowColor_successor hB hb (predecessor hB j)
  rw [successor_predecessor] at h
  have hh := congrArg Bool.not h
  simpa only [Bool.not_not] using hh.symm

/-- Genuine endpoint colors of a subdivided first-axis edge. -/
def startColor {K B : Nat} (turns : Grid K B→Bool) (i : Fin K) (j : Fin B) : Bool :=
  rowColor j ^^ turns (i,j)
def endColor {K B : Nat} (hK : 0<K) (turns : Grid K B→Bool) (i : Fin K) (j : Fin B) : Bool :=
  !(rowColor j ^^ turns (successor hK i,j))

/-- Literal fine-edge coloring: only an internal threshold z can change color. -/
def edgeColor {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z : Fin A) : FineEdge K A B→Bool
  | .inl (x,j) =>
      let p := AnchoredEmbedding.positionDecode hA x
      if p.2.val<z.val then startColor turns p.1 j else endColor hK turns p.1 j
  | .inr (_,j) => rowColor j

/-- Actual degree-two mark, before any cyclic ordering is chosen. -/
def IsMark {K A B : Nat} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A)
    (v : Fine K A B) : Prop :=
  ∃i : Fin K, ∃j : Fin B,
    v=(AnchoredEmbedding.positionEncode i z,j) ∧ turns (i,j)=turns (successor hK i,j)

theorem endpoint_change_iff {K B : Nat} (hK : 0<K) (turns : Grid K B→Bool)
    (i : Fin K) (j : Fin B) :
    startColor turns i j≠endColor hK turns i j ↔ turns (i,j)=turns (successor hK i,j) := by
  cases hr : rowColor j <;> cases ht : turns (i,j) <;>
    cases ht' : turns (successor hK i,j) <;> simp [startColor,endColor,hr,ht,ht']

theorem edgeColor_before {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z d : Fin A) (i : Fin K) (j : Fin B)
    (hd : d.val<z.val) :
    edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i d,j))=
      startColor turns i j := by
  simp only [edgeColor,AnchoredEmbedding.positionDecode_encode,ite_eq_left hd]

theorem edgeColor_after {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z d : Fin A) (i : Fin K) (j : Fin B)
    (hd : z.val≤d.val) :
    edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i d,j))=
      endColor hK turns i j := by
  simp only [edgeColor,AnchoredEmbedding.positionDecode_encode,ite_eq_right (by omega : ¬d.val<z.val)]

/-- The marked vertex is exactly the local color change, not an arbitrary
chosen representative with unproved traversal behavior. -/
theorem internal_change_iff {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z : Fin A) (hz : 0<z.val) (i : Fin K) (j : Fin B) :
    edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i ⟨z.val-1,by omega⟩,j))≠
      edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i z,j)) ↔
      IsMark hK turns z (AnchoredEmbedding.positionEncode i z,j) := by
  rw [edgeColor_before hK hA turns z _ i j (by simp only; omega),edgeColor_after hK hA turns z z i j (by omega)]
  rw [endpoint_change_iff]
  constructor
  · intro h; exact ⟨i,j,rfl,h⟩
  · rintro ⟨i',j',he,ht⟩
    have hx := congrArg Prod.fst he
    have hcoords := AnchoredEmbedding.positionEncode_injective hA (a₁ := (i,z)) (a₂ := (i',z)) hx
    have hi := congrArg Prod.fst hcoords
    have hj := congrArg Prod.snd he
    simp only at hi hj
    subst i'; subst j'
    exact ht

/-- Away from the threshold, two consecutive internal edge colors agree. -/
theorem internal_no_change {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z d : Fin A) (hd : 0<d.val) (hzd : d≠z)
    (i : Fin K) (j : Fin B) :
    edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i ⟨d.val-1,by omega⟩,j))=
      edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i d,j)) := by
  have hn : d.val≠z.val := fun he => hzd (Fin.ext he)
  by_cases hlt : d.val<z.val
  · rw [edgeColor_before hK hA turns z _ i j (by simp only; omega),edgeColor_before hK hA turns z d i j hlt]
  · rw [edgeColor_after hK hA turns z _ i j (by simp only; omega),edgeColor_after hK hA turns z d i j (by omega)]

theorem mark_encode_iff {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z d : Fin A) (i : Fin K) (j : Fin B) :
    IsMark hK turns z (AnchoredEmbedding.positionEncode i d,j) ↔
      d=z ∧ turns (i,j)=turns (successor hK i,j) := by
  constructor
  · rintro ⟨i',j',he,ht⟩
    have hx := AnchoredEmbedding.positionEncode_injective hA (a₁ := (i,d)) (a₂ := (i',z))
      (congrArg Prod.fst he)
    have hi := congrArg Prod.fst hx
    have hd := congrArg Prod.snd hx
    have hj := congrArg Prod.snd he
    simp only at hi hd hj
    subst i'; subst j'
    exact ⟨hd,ht⟩
  · rintro ⟨rfl,ht⟩
    exact ⟨i,j,rfl,ht⟩

/-- Complete local rule at any internal fine vertex. -/
theorem internal_change_at_iff {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z d : Fin A) (hz : 0<z.val) (hd : 0<d.val)
    (i : Fin K) (j : Fin B) :
    edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i ⟨d.val-1,by omega⟩,j))≠
      edgeColor hK hA turns z (.inl (AnchoredEmbedding.positionEncode i d,j)) ↔
      IsMark hK turns z (AnchoredEmbedding.positionEncode i d,j) := by
  by_cases he : d=z
  · subst d; exact internal_change_iff hK hA turns z hz i j
  · have hc := internal_no_change hK hA turns z d hd he i j
    rw [mark_encode_iff hK hA]
    simp only [hc,ne_eq,not_true_eq_false,he,false_and]

/-- Every literal mark is outside the grid, and already has a unique
numeric fine occurrence by AACFineGeometry.internal_clock_owner. -/
theorem mark_nonGrid {K A B : Nat} (hK : 0<K) (hA : 0<A)
    (turns : Grid K B→Bool) (z : Fin A) (hz : 0<z.val)
    (v : Fine K A B) (hv : IsMark hK turns z v) : NonGrid hA v := by
  obtain ⟨i,j,rfl,ht⟩ := hv
  apply (nonGrid_iff hA _).2
  simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt z.isLt]
  omega

/-- The first actual outgoing fine edge has the endpoint port color. -/
theorem segment_first_color {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) (turns : Grid K B→Bool) (z : Fin A) (hz : 0<z.val)
    (s : State K B) :
    edgeColor hK hA turns z (segmentLabel hK hA hB s ⟨0,weight_pos hA s.2.2⟩)=
      portColor turns s := by
  rcases s with ⟨i,j,p⟩
  cases p
  · simp only [segmentLabel,edgeColor,AnchoredEmbedding.positionDecode_encode]
    rw [ite_eq_left hz]
    rfl
  · rfl
  · have hl : z.val≤A-1 := by have := z.isLt; omega
    simp only [segmentLabel,edgeColor,AnchoredEmbedding.positionDecode_encode]
    rw [ite_eq_right (show ¬A-1-0<z.val by omega)]
    simp only [endColor,successor_predecessor]
    rfl
  · simpa only [segmentLabel,edgeColor,portColor,rowColor] using rowColor_predecessor hB hb j

/-- The last edge of a subdivision has the arrival port color at its actual
crossed endpoint. This includes reversed base edges and second-axis seams. -/
theorem segment_last_color {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) (turns : Grid K B→Bool) (z : Fin A) (hz : 0<z.val)
    (s : State K B) :
    edgeColor hK hA turns z (segmentLabel hK hA hB s
      ⟨weight A s.2.2-1,by have := weight_pos hA s.2.2; omega⟩)=
      portColor turns (cross hK hB s) := by
  rcases s with ⟨i,j,p⟩
  cases p
  · have hl : z.val≤A-1 := by have := z.isLt; omega
    simp only [segmentLabel,weight,edgeColor,AnchoredEmbedding.positionDecode_encode]
    rw [ite_eq_right (show ¬A-1<z.val by omega)]
    rfl
  · simp only [segmentLabel,edgeColor,cross,portColor]
    change rowColor j = !rowColor (successor hB j)
    rw [rowColor_successor hB hb,Bool.not_not]
  · have hd : A-1-(A-1)=0 := by omega
    simp only [segmentLabel,weight,edgeColor,AnchoredEmbedding.positionDecode_encode,hd]
    rw [ite_eq_left hz]
    rfl
  · simp only [segmentLabel,edgeColor,cross,portColor]
    rfl

/-- Internal steps in either directed subdivision change color exactly at
literal turn-agreement marks. Horizontal subdivisions have no internal step. -/
theorem segment_change_iff {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (turns : Grid K B→Bool) (z : Fin A) (hz : 0<z.val)
    (s : State K B) (k : Fin (weight A s.2.2)) (hk : k.val+1<weight A s.2.2) :
    edgeColor hK hA turns z (segmentLabel hK hA hB s k)≠
      edgeColor hK hA turns z (segmentLabel hK hA hB s ⟨k.val+1,hk⟩) ↔
      IsMark hK turns z (segment hK hA hB s ⟨k.val+1,by omega⟩) := by
  rcases s with ⟨i,j,p⟩
  cases p
  · have hlt : k.val+1<A := by simpa only [weight] using hk
    let d : Fin A := ⟨k.val+1,hlt⟩
    have hprev : (⟨d.val-1,by have := d.isLt; omega⟩ : Fin A)=k := Fin.ext (by simp [d])
    have hc := internal_change_at_iff hK hA turns z d hz (by simp [d]) i j
    rw [hprev] at hc
    simp only [segmentLabel,segment,dite_eq_left hlt]
    exact hc
  · simp only [weight] at hk
    omega
  · have hlt : k.val+1<A := by simpa only [weight] using hk
    let d : Fin A := ⟨A-1-k.val,by omega⟩
    have hd : 0<d.val := by dsimp [d]; omega
    have hprev : A-1-(k.val+1)=d.val-1 := by dsimp [d]; omega
    have hpoint : A-(k.val+1)=d.val := by dsimp [d]; omega
    have hkn : k.val+1≠0 := by omega
    have hc := internal_change_at_iff hK hA turns z d hz hd (predecessor hK i) j
    simp only [segmentLabel,segment,dite_eq_right hkn,hprev,hpoint]
    exact ne_comm.trans hc
  · simp only [weight] at hk
    omega

/-- Coarse seams in the actual traversal never create marks at grids. -/
theorem coarse_seam_color {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (z : Fin A) (hz : 0<z.val) (n : Fin N) :
    edgeColor hK hA turns z (segmentLabel hK hA hB (atPair turns (C.point n))
      ⟨weight A (atPair turns (C.point n)).2.2-1,
        by have := weight_pos hA (atPair turns (C.point n)).2.2; omega⟩)=
    edgeColor hK hA turns z (segmentLabel hK hA hB
      (atPair turns (C.point (successor hN n)))
      ⟨0,weight_pos hA (atPair turns (C.point (successor hN n))).2.2⟩) := by
  rw [segment_last_color hK hA hB hb turns z hz,segment_first_color hK hA hB hb turns z hz,
    pair_color,←C.next n]
  rfl

/-- Literal color clock on the expanded directed edge occurrences. -/
def expandedColor {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (z : Fin A) (p : ExpandedIndex (A := A) C) : Bool :=
  edgeColor hK hA turns z (expandedLabel hK hA hB C p)

/-- Exact color-change detection on the actual ragged traversal, including
its last-to-first seam. -/
theorem expanded_change_iff {K A B N : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (z : Fin A) (hz : 0<z.val) (p : ExpandedIndex (A := A) C) :
    expandedColor hK hA hB C z p≠expandedColor hK hA hB C z (expandedNext hA C p) ↔
      IsMark hK turns z (expandedVertex hK hA hB C (expandedNext hA C p)) := by
  rcases p with ⟨n,k⟩
  by_cases hk : k.val+1<weight A (atPair turns (C.point n)).2.2
  · have hnxt : expandedNext hA C ⟨n,k⟩=⟨n,⟨k.val+1,hk⟩⟩ := by
      unfold expandedNext
      exact dite_eq_left hk
    rw [hnxt]
    exact segment_change_iff hK hA hB turns z hz (atPair turns (C.point n)) k hk
  · have hnxt : expandedNext hA C ⟨n,k⟩=⟨successor hN n,⟨0,weight_pos hA _⟩⟩ := by
      unfold expandedNext
      exact dite_eq_right hk
    have hlast : k.val=weight A (atPair turns (C.point n)).2.2-1 := by have := k.isLt; omega
    have hc := coarse_seam_color hK hA hB hb C z hz n
    have he : k=⟨weight A (atPair turns (C.point n)).2.2-1,
        by have := weight_pos hA (atPair turns (C.point n)).2.2; omega⟩ := Fin.ext hlast
    have hgrid : expandedVertex hK hA hB C (expandedNext hA C ⟨n,k⟩)=
        gridPoint hA (stateVertex (C.point (successor hN n))) := by
      rw [hnxt]
      change segment hK hA hB (atPair turns (C.point (successor hN n))) ⟨0,_⟩=_
      rw [segment_start]
      rfl
    have hnot : ¬IsMark hK turns z (expandedVertex hK hA hB C (expandedNext hA C ⟨n,k⟩)) := by
      intro hm
      exact mark_nonGrid hK hA turns z hz _ hm _ hgrid
    rw [hnxt] at hnot
    rw [hnxt]
    change edgeColor hK hA turns z (segmentLabel hK hA hB (atPair turns (C.point n)) k)≠_ ↔ _
    rw [he]
    exact iff_of_false (fun hn => hn hc) hnot

/-- Actual numeric edge-color word, with no assumed interval structure. -/
def numericColor {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (z : Fin A) (n : Fin E) : Bool :=
  edgeColor hK hA turns z (AACFineClock.fineLabel hK hA hB C hE n)

theorem numeric_change_iff {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (z : Fin A) (hz : 0<z.val) (n : Fin E) :
    numericColor hK hA hB C hE z n≠numericColor hK hA hB C hE z (successor hpos n) ↔
      IsMark hK turns z (AACFineClock.fineVertex hK hA hB C hE (successor hpos n)) := by
  have hc := expanded_change_iff hK hA hB hb C z hz (AACFineClock.exactPosition C hE n)
  rw [AACFineClock.exactPosition_next hA C hE hpos n] at hc
  exact hc

/-- Literal fine color at a grid occurrence equals its concrete coarse port
color; this is the missing local link used in geometric collisions. -/
theorem numeric_grid_color {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (z : Fin A) (hz : 0<z.val)
    (n : Fin E) (g : Grid K B)
    (he : AACFineClock.fineVertex hK hA hB C hE n=gridPoint hA g) :
    numericColor hK hA hB C hE z n=
      portColor turns (C.point (AACFineClock.exactPosition C hE n).1) := by
  let p := AACFineClock.exactPosition (A := A) C hE n
  have hp := expanded_grid_start hK hA hB C p g he
  have hk : p.2=⟨0,weight_pos hA (atPair turns (C.point p.1)).2.2⟩ := Fin.ext hp.1
  change edgeColor hK hA turns z (segmentLabel hK hA hB (atPair turns (C.point p.1)) p.2)=_
  rw [hk,segment_first_color hK hA hB hb turns z hz,pair_color]

/-- Run number derived from actual color changes in a word, not supplied by
an interval-existence hypothesis. -/
def changeRank (color : Nat→Bool) : Nat→Nat
  | 0 => 0
  | n+1 => changeRank color n + if color n=color (n+1) then 0 else 1

theorem color_changeRank (color : Nat→Bool) (n : Nat) :
    color n=PairedLayers.flipN (changeRank color n) (color 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases he : color n=color (n+1)
    · rw [changeRank,ite_eq_left he,Nat.add_zero,←he]
      exact ih
    · have hn : color (n+1)=!color n := by
        cases h : color n <;> cases h' : color (n+1) <;> simp_all
      simp only [changeRank,ite_eq_right he,Nat.add_one,PairedLayers.flipN]
      rw [PairedLayers.flipN_not,←ih,hn]

theorem flipN_parity (n : Nat) (b : Bool) :
    PairedLayers.flipN n b=if n%2=0 then b else !b := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    rw [PairedLayers.flipN,ih]
    have hm := Nat.mod_lt n (by decide : 0<2)
    by_cases he : n%2=0
    · have hn : (n+1)%2≠0 := by omega
      simp only [ite_eq_left he,ite_eq_right hn]
    · have hn : (n+1)%2=0 := by omega
      simp only [ite_eq_right he,ite_eq_left hn,Bool.not_not]

theorem changeRank_parity {color : Nat→Bool} {n m : Nat} (hc : color n≠color m) :
    changeRank color n%2≠changeRank color m%2 := by
  intro he
  apply hc
  rw [color_changeRank color n,color_changeRank color m,flipN_parity,flipN_parity,he]

/-- Uniform extension of the actual cyclic numeric color word. -/
def cyclicColor {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (z : Fin A) (n : Nat) : Bool :=
  numericColor hK hA hB C hE z ⟨n%E,Nat.mod_lt _ hpos⟩

/-- Actual fine collisions now force opposite color-run parity. No collision
law, mark pairing, or final output simplicity is assumed. -/
theorem fine_collision_run_parity {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (AACFineClock.fineLabel hK hA hB C hE))
    (hcoarse : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (z : Fin A) (hz : 0<z.val) (n m : Fin E)
    (he : AACFineClock.fineVertex hK hA hB C hE n=AACFineClock.fineVertex hK hA hB C hE m) :
    n=m ∨ changeRank (cyclicColor hK hA hB C hE hpos z) n.val%2≠
      changeRank (cyclicColor hK hA hB C hE hpos z) m.val%2 := by
  rcases fine_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hlabel hcoarse n m he with hn|⟨g,hg,hc⟩
  · exact Or.inl hn
  · right
    apply changeRank_parity
    have hn := numeric_grid_color hK hA hB hb C hE z hz n g hg
    have hm := numeric_grid_color hK hA hB hb C hE z hz m g (he.symm.trans hg)
    simpa only [cyclicColor,Nat.mod_eq_of_lt n.isLt,Nat.mod_eq_of_lt m.isLt,Fin.eta,hn,hm] using hc

/-- The total number of actual changes in any cyclic binary word is even. -/
theorem cyclic_changeRank_even {E : Nat} (hE : 0<E) (color : Fin E→Bool) :
    changeRank (fun n => color ⟨n%E,Nat.mod_lt _ hE⟩) E%2=0 := by
  let c : Nat→Bool := fun n => color ⟨n%E,Nat.mod_lt _ hE⟩
  have hc : c E=c 0 := by simp only [c,Nat.mod_self,Nat.zero_mod]
  have hr := color_changeRank c E
  rw [hc,flipN_parity] at hr
  by_cases he : changeRank c E%2=0
  · exact he
  · rw [ite_eq_right he] at hr
    cases hb : c 0 <;> simp [hb] at hr

/-- The concrete ordered list of mark positions is selected from the genuine
fine Euler clock, using the already proved color-change test. -/
def markPositions {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (z : Fin A) : List (Fin E) :=
  (List.finRange E).filter (fun n => decide
    (numericColor hK hA hB C hE z (predecessor hpos n)≠numericColor hK hA hB C hE z n))

theorem mem_markPositions {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (z : Fin A) (hz : 0<z.val) (n : Fin E) :
    n∈markPositions hK hA hB C hE hpos z ↔
      IsMark hK turns z (AACFineClock.fineVertex hK hA hB C hE n) := by
  have hc := numeric_change_iff hK hA hB hb C hE hpos z hz (predecessor hpos n)
  rw [successor_predecessor] at hc
  simpa only [markPositions,List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq] using hc

theorem markPositions_nodup {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (z : Fin A) :
    (markPositions hK hA hB C hE hpos z).Nodup :=
  (List.nodup_finRange E).filter _

/-- Physical marked vertices also occur once; position distinctness alone
would not suffice because the ambient Euler clock repeats grids. -/
theorem marked_collision {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (AACFineClock.fineLabel hK hA hB C hE))
    (z : Fin A) (hz : 0<z.val) (n m : Fin E)
    (hn : n∈markPositions hK hA hB C hE hpos z)
    (he : AACFineClock.fineVertex hK hA hB C hE n=AACFineClock.fineVertex hK hA hB C hE m) : n=m := by
  have hm := (mem_markPositions hK hA hB hb C hE hpos z hz n).mp hn
  exact nonGrid_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hlabel n m
    (mark_nonGrid hK hA turns z hz _ hm) he

/-- The cumulative run number is literally the number of preceding color
changes; no externally specified interval count is used. -/
theorem changeRank_count (color : Nat→Bool) (n : Nat) :
    changeRank color n=(List.range n).countP (fun i => decide (color i≠color (i+1))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [changeRank,ih,List.range_succ,List.countP_append]
    by_cases he : color n=color (n+1) <;> simp [he]

/-- Ordered physical marks obtained from the literal numeric traversal. -/
def markWord {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (z : Fin A) : List (Fine K A B) :=
  (markPositions hK hA hB C hE hpos z).map (AACFineClock.fineVertex hK hA hB C hE)

theorem markWord_nodup {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (AACFineClock.fineLabel hK hA hB C hE))
    (z : Fin A) (hz : 0<z.val) : (markWord hK hA hB C hE hpos z).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp_of_mem
    (fun hn _ hne he => hne (marked_collision hK hA hB h3 hB3 hb C hE hpos hE2 hlabel z hz _ _ hn he))
    (markPositions_nodup hK hA hB C hE hpos z)

/-- Actual incoming color-change flag of a finite cyclic word. -/
def cyclicFlag {E : Nat} (hE : 0<E) (color : Fin E→Bool) (n : Fin E) : Bool :=
  decide (color (predecessor hE n)≠color n)

/-- At any nonterminal clock position, the run number is exactly the number
of preceding marked positions, with the explicit contribution at position 0.
After cutting at a genuine mark this contribution is 1. -/
theorem rank_prefix_flags {E : Nat} (hE : 0<E) (color : Fin E→Bool) (n : Nat) (hn : n<E) :
    changeRank (fun i => color ⟨i%E,Nat.mod_lt _ hE⟩) n +
      (cyclicFlag hE color ⟨0,hE⟩).toNat =
        Profile.prefixCount (cyclicFlag hE color) (n+1) := by
  induction n with
  | zero => simp only [changeRank,Profile.prefixCount,Profile.indicator,dite_eq_left hE,Nat.zero_add]
  | succ n ih =>
    have hn' : n<E := by omega
    have hp : predecessor hE (⟨n+1,hn⟩ : Fin E)=⟨n,hn'⟩ := by
      have hs : successor hE (⟨n,hn'⟩ : Fin E)=⟨n+1,hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      rw [←hs,predecessor_successor]
    have hi : Profile.indicator (cyclicFlag hE color) (n+1)=
        (decide (color ⟨n,hn'⟩≠color ⟨n+1,hn⟩)).toNat := by
      simp only [Profile.indicator,dite_eq_left hn,cyclicFlag,hp]
    have ih' := ih hn'
    rw [Profile.prefixCount,hi,←ih',changeRank]
    simp only [Nat.mod_eq_of_lt hn',Nat.mod_eq_of_lt hn]
    by_cases he : color ⟨n,hn'⟩=color ⟨n+1,hn⟩ <;>
      simp [he,Nat.add_comm,Nat.add_left_comm]

#print axioms rank_prefix_flags
#print axioms markWord_nodup
#print axioms cyclic_changeRank_even
#print axioms marked_collision
#print axioms fine_collision_run_parity
#print axioms numeric_change_iff
#print axioms coarse_seam_color
#print axioms internal_change_iff
#print axioms internal_no_change
end ErdePaths.AACMarkIntervals
