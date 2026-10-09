import ErdePaths.AACFoldEdgeLedger
import ErdePaths.AACFineGeometry
import ErdePaths.ForkTransfer
import ErdePaths.HamiltonOrient

namespace ErdePaths.AACFoldFork
open SquareLift PairedLayers LayerPartition AACIntervalSplit AACFoldGeometry AACFoldOrder AACUnfold
variable {Y X : Type} {R : X→X→Prop} {χ : X→Bool} {r q : Nat} {hr : 0<r}

/-- Every assigned mark is an actual common physical vertex of both folded
outputs. Arrival/departure are chosen from the real input matching prefix. -/
theorem mark_common (I : Intervals Y q) (C : CycleData X R χ r hr)
    (layers : Fin q→CycleData X R χ r hr) (selectors : Fin q→Bool)
    (j : Fin q) (x : X) (color : Bool) :
    ∃p : AACUnfold.Position I r, AACUnfold.vertex I C layers selectors color p=(I.mark j,x) := by
  obtain ⟨⟨t,k,b⟩,he⟩ := commonTour_surjective C layers selectors color (j,x)
  have hj : k=j := congrArg Prod.fst he
  subst k
  refine ⟨Sum.inl (t,j,b),?_⟩
  change (I.mark j,(commonTour C layers selectors color (t,j,b)).2)=(I.mark j,x)
  have hx : (commonTour C layers selectors color (t,j,b)).2=x := congrArg (fun p : Fin q×X=>p.2) he
  exact Prod.ext rfl hx

/-- At a unique physical base interior the owning output is determined by
its actual chronological gap ordinal and the physical X bipartition. -/
theorem interior_mem_iff (I : Intervals Y q) (C : CycleData X R χ r hr)
    (layers : Fin q→CycleData X R χ r hr) (selectors : Fin q→Bool)
    (o : Occurrence I) (hu : ∀p, I.physical p=I.physical o→p=o)
    (x : X) (color : Bool) :
    (∃p : AACUnfold.Position I r, AACUnfold.vertex I C layers selectors color p=(I.physical o,x)) ↔
      χ x= !flipN o.1.val color := by
  constructor
  · rintro ⟨p,hp⟩
    cases p with
    | inl p =>
      have he := congrArg Prod.fst hp
      exact False.elim (I.mark_exclusion o p.2.1 he.symm)
    | inr p =>
      have ho : p.1=o := hu p.1 (congrArg Prod.fst hp)
      have hx := congrArg Prod.snd hp
      change departure C layers selectors color p.1.1 p.2=x at hx
      rw [←hx,departure_side C layers selectors color p.1.1 p.2,ho]
  · intro hx
    obtain ⟨t,ht⟩ := departure_covers_side C layers selectors color o.1 x hx
    exact ⟨Sum.inr (o,t),Prod.ext rfl ht⟩

/-- Complementary folded outputs cannot both contain the same X vertex at
a uniquely occurring interior. This is proved membership, not a fork oracle. -/
theorem interior_exclusive (I : Intervals Y q) (C : CycleData X R χ r hr)
    (layers : Fin q→CycleData X R χ r hr) (selectors : Fin q→Bool)
    (o : Occurrence I) (hu : ∀p, I.physical p=I.physical o→p=o)
    (x : X) (color : Bool)
    (hp : ∃p : AACUnfold.Position I r, AACUnfold.vertex I C layers selectors color p=(I.physical o,x)) :
    ∀p, AACUnfold.vertex I C layers selectors (!color) p≠(I.physical o,x) := by
  have hs := (interior_mem_iff I C layers selectors o hu x color).mp hp
  intro p he
  have ht := (interior_mem_iff I C layers selectors o hu x (!color)).mp ⟨p,he⟩
  rw [flipN_not] at ht
  cases hh : flipN o.1.val color <;> simp only [hh,Bool.not_false,Bool.not_true] at hs ht
  · exact Bool.noConfusion (hs.symm.trans ht)
  · exact Bool.noConfusion (hs.symm.trans ht)

/-- Opposite actual interval parities give opposite output owners for the
same physical X vertex, with both neighbors excluded from the other output. -/
theorem opposite_interiors (I : Intervals Y q) (C : CycleData X R χ r hr)
    (layers : Fin q→CycleData X R χ r hr) (selectors : Fin q→Bool)
    (o p : Occurrence I) (hu : ∀v, I.physical v=I.physical o→v=o)
    (hv : ∀v, I.physical v=I.physical p→v=p) (hpar : o.1.val%2≠p.1.val%2) (x : X) :
    ∃color,
      (∃a, AACUnfold.vertex I C layers selectors color a=(I.physical o,x)) ∧
      (∃b, AACUnfold.vertex I C layers selectors (!color) b=(I.physical p,x)) ∧
      (∀a, AACUnfold.vertex I C layers selectors (!color) a≠(I.physical o,x)) ∧
      (∀b, AACUnfold.vertex I C layers selectors color b≠(I.physical p,x)) := by
  let color := flipN o.1.val (!χ x)
  have hself (n : Nat) (b : Bool) : flipN n (flipN n b)=b := by
    induction n generalizing b with
    | zero => rfl
    | succ n ih => change flipN n (!(flipN n (!b)))=b; rw [←flipN_not,Bool.not_not,ih]
  have hs : χ x= !flipN o.1.val color := by simp only [color,hself,Bool.not_not]
  have hpflip : flipN p.1.val (!color)=flipN o.1.val color := by
    rw [flipN_mod,flipN_mod]
    have ho := Nat.mod_lt o.1.val (by decide : 0<2)
    have hp := Nat.mod_lt p.1.val (by decide : 0<2)
    by_cases hz : o.1.val%2=0
    · have hn : p.1.val%2≠0 := by omega
      simp only [hz,hn,↓reduceIte,Bool.not_not]
    · have hz' : p.1.val%2=0 := by omega
      simp only [hz,hz',↓reduceIte]
  have ht : χ x= !flipN p.1.val (!color) := by rw [hpflip]; exact hs
  have ha := (interior_mem_iff I C layers selectors o hu x color).mpr hs
  have hb := (interior_mem_iff I C layers selectors p hv x (!color)).mpr ht
  refine ⟨color,ha,hb,interior_exclusive I C layers selectors o hu x color ha,?_⟩
  simpa only [Bool.not_not] using interior_exclusive I C layers selectors p hv x (!color) hb

section Actual
variable {E : Nat} (hE : 0<E) (base : Fin E→Y) (baseColor : Fin E→Bool)
variable (hcut : AACMarkIntervals.cyclicFlag hE baseColor ⟨0,hE⟩=true)
variable (hmark : ∀n m, AACMarkIntervals.cyclicFlag hE baseColor n=true→base n=base m→n=m)
variable (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m)
local notation "S" => AACMarkIntervals.cyclicFlag hE baseColor
variable (C : CycleData X R χ r hr)
variable (layers : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→CycleData X R χ r hr)
variable (selectors : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))→Bool)
variable (hq : 0<Profile.cardinality (AACMarkIntervals.cyclicFlag hE baseColor))
include hcut hmark hcollision layers selectors hq

/-- Literal numeric folded vertices contain every X vertex at every actual
mark in BOTH outputs; positions are constructed through checked inverses. -/
theorem numeric_mark_common (j : Fin (Profile.cardinality S)) (x : X) (color : Bool) :
    ∃n, foldVertex S base C layers selectors color (AACFoldClock.numeric S hq n)=
      (base (markIndex S j),x) := by
  let I := split hE base baseColor hcut hmark hcollision
  obtain ⟨p,hp⟩ := mark_common I C layers selectors j x color
  obtain ⟨a,ha⟩ := position_surjective S p
  obtain ⟨n,hn⟩ := AACFoldClock.numeric_surjective S hq a
  refine ⟨n,?_⟩
  rw [hn,←unfold_vertex_position hE base baseColor hcut hmark hcollision C layers selectors color a,ha]
  exact hp

/-- Faithful numeric membership criterion at an actually unique unmarked
chronological base occurrence. No output membership is a hypothesis. -/
theorem numeric_interior_mem_iff (o : InteriorIndex S)
    (hu : ∀n, base n=base (interiorIndex S o)→n=interiorIndex S o) (x : X) (color : Bool) :
    (∃n, foldVertex S base C layers selectors color (AACFoldClock.numeric S hq n)=
      (base (interiorIndex S o),x)) ↔ χ x= !flipN o.1.val color := by
  let I := split hE base baseColor hcut hmark hcollision
  have hi : ∀p : Occurrence I, I.physical p=I.physical o→p=o := by
    intro p hp
    exact interiorIndex_injective S (hu _ hp)
  have hs := interior_mem_iff I C layers selectors o hi x color
  refine Iff.trans ?_ hs
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨position S (AACFoldClock.numeric S hq n),?_⟩
    rw [unfold_vertex_position]
    exact hn
  · rintro ⟨p,hp⟩
    obtain ⟨a,ha⟩ := position_surjective S p
    obtain ⟨n,hn⟩ := AACFoldClock.numeric_surjective S hq a
    refine ⟨n,?_⟩
    rw [hn,←unfold_vertex_position hE base baseColor hcut hmark hcollision C layers selectors color a,ha]
    exact hp

/-- The two buffered neighbors of the SECOND actual chronological mark
have literal gap ordinals zero and one. The hypotheses concern only input
base vertices and flags; no folded membership or fork is assumed. -/
theorem buffered_second_mark (hcard : 3≤Profile.cardinality S)
    (hleft : ∀(n : Fin E), n.val+1=(markIndex S ⟨1,by omega⟩).val→S n=false)
    (hright : ∀(n : Fin E), n.val=(markIndex S ⟨1,by omega⟩).val+1→S n=false)
    (hunique : ∀(n : Fin E),
      (n.val+1=(markIndex S ⟨1,by omega⟩).val ∨ n.val=(markIndex S ⟨1,by omega⟩).val+1)→
      ∀m,base m=base n→m=n) (x : X) :
    ∃(a b : Fin E) (color : Bool),
      a.val+1=(markIndex S ⟨1,by omega⟩).val ∧ b.val=(markIndex S ⟨1,by omega⟩).val+1 ∧
      (∃n,foldVertex S base C layers selectors color (AACFoldClock.numeric S hq n)=(base a,x)) ∧
      (∃n,foldVertex S base C layers selectors (!color) (AACFoldClock.numeric S hq n)=(base b,x)) ∧
      (∀n,foldVertex S base C layers selectors (!color) (AACFoldClock.numeric S hq n)≠(base a,x)) ∧
      (∀n,foldVertex S base C layers selectors color (AACFoldClock.numeric S hq n)≠(base b,x)) := by
  let j : Fin (Profile.cardinality S) := ⟨1,by omega⟩
  let m := markIndex S j
  have hpre : Profile.prefixCount S m.val=1 := marked_level_before S j
  have hmpos : 0<m.val := by
    by_cases hh : m.val=0
    · rw [hh] at hpre
      simp only [Profile.prefixCount] at hpre
      omega
    · omega
  have hmright : m.val+1<E := by
    have ho := markIndex_order S j (⟨2,by omega⟩ : Fin (Profile.cardinality S)) (by simp [j])
    have hi := (markIndex S (⟨2,by omega⟩ : Fin (Profile.cardinality S))).isLt
    omega
  let a : Fin E := ⟨m.val-1,by have := m.isLt; omega⟩
  let b : Fin E := ⟨m.val+1,hmright⟩
  have ha : a.val+1=m.val := by dsimp [a]; omega
  have hb : b.val=m.val+1 := rfl
  have haf : S a=false := hleft a ha
  have hbf : S b=false := hright b hb
  obtain ⟨o,ho⟩ := interior_complete hE S hcut a haf
  obtain ⟨p,hp⟩ := interior_complete hE S hcut b hbf
  have hoc : o.1.val=0 := by
    have hs := (interiorIndex_spec S o).2
    rw [ho,ha] at hs
    omega
  have hpc : p.1.val=1 := by
    have hs := (interiorIndex_spec S p).2
    rw [hp] at hs
    have hmstep := (markIndex_spec S j).2
    have hnext : Profile.prefixCount S (b.val+1)=Profile.prefixCount S b.val := by
      simp only [Profile.prefixCount,Profile.indicator,dite_eq_left b.isLt,hbf,Bool.toNat_false,Nat.add_zero]
    rw [hnext,hb] at hs
    change Profile.prefixCount S (m.val+1)=p.1.val+1 at hs
    change Profile.prefixCount S (m.val+1)=2 at hmstep
    omega
  have hua : ∀n,base n=base (interiorIndex S o)→n=interiorIndex S o := by
    rw [ho]
    exact hunique a (Or.inl ha)
  have hub : ∀n,base n=base (interiorIndex S p)→n=interiorIndex S p := by
    rw [hp]
    exact hunique b (Or.inr hb)
  let color := !χ x
  have hsa : χ x= !flipN o.1.val color := by simp [hoc,color,flipN]
  have hsb : χ x= !flipN p.1.val (!color) := by simp [hpc,color,flipN]
  have hma := (numeric_interior_mem_iff hE base baseColor hcut hmark hcollision C layers selectors hq o hua x color).mpr hsa
  have hmb := (numeric_interior_mem_iff hE base baseColor hcut hmark hcollision C layers selectors hq p hub x (!color)).mpr hsb
  rw [ho] at hma
  rw [hp] at hmb
  refine ⟨a,b,color,ha,hb,hma,hmb,?_,?_⟩
  · intro n hn
    have hs := (numeric_interior_mem_iff hE base baseColor hcut hmark hcollision C layers selectors hq o hua x (!color)).mp
      ⟨n,by rw [ho]; exact hn⟩
    simp only [hoc,flipN] at hs
    dsimp [color] at hs
    cases hh : χ x <;> simp [hh] at hs
  · intro n hn
    have hs := (numeric_interior_mem_iff hE base baseColor hcut hmark hcollision C layers selectors hq p hub x color).mp
      ⟨n,by rw [hp]; exact hn⟩
    simp only [hpc,flipN] at hs
    dsimp [color] at hs
    cases hh : χ x <;> simp [hh] at hs

end Actual

/-- Actual fine Euler internal vertices remain unique after transport
through real source and H Hamilton clocks. This supplies the uniqueness
hypothesis above for the offset-one/three buffered neighbors, uniformly. -/
theorem physical_internal_unique {U V : Type} {K A B N E : Nat}
    (hK : 0<K) (hA : 0<A) (hB : 0<B) (h3 : 3≤K*A) (hB3 : 3≤B)
    {hN : 0<N} {turns : AACTransition.Grid K B→Bool}
    (O : AACMerge.Orbit (AACTransition.State K B) (AACTransition.transition hK hB turns) N hN)
    (hE : (AACFine.indexList (A:=A) O).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (AACFineClock.fineLabel hK hA hB O hE))
    (G : SourceClock.ClockData U (K*A)) (H : SourceClock.ClockData V B)
    (i : Fin K) (z : Fin A) (hz : 0<z.val) (j : Fin B) (n m : Fin E)
    (hn : AACFineGeometry.physical G H (AACFineClock.fineVertex hK hA hB O hE n)=
      AACFineGeometry.physical G H (AnchoredEmbedding.positionEncode i z,j))
    (hm : AACFineGeometry.physical G H (AACFineClock.fineVertex hK hA hB O hE m)=
      AACFineGeometry.physical G H (AnchoredEmbedding.positionEncode i z,j)) : n=m :=
  AACFineGeometry.internal_clock_collision hK hA hB h3 hB3 O hE hpos hE2 hinj i z hz j n m
    (AACFineGeometry.physical_injective G H hn) (AACFineGeometry.physical_injective G H hm)

/-- The literal two neighbors of a buffered offset-two mark are offset one
and offset three in the SAME subdivided base edge. Both are internal and
cannot be marks, independently of the turn pattern. -/
theorem buffered_adjacent {K A B : Nat} (hK : 0<K) (hA4 : 4≤A) (hB : 0<B)
    (turns : AACTransition.Grid K B→Bool) (i : Fin K) (j : Fin B)
    (w : AACTransition.Fine K A B)
    (hadj : AACTransition.Adjacent hK (by omega) hB
      (AnchoredEmbedding.positionEncode i (⟨2,by omega⟩ : Fin A),j) w) :
    (w=(AnchoredEmbedding.positionEncode i (⟨1,by omega⟩ : Fin A),j) ∨
      w=(AnchoredEmbedding.positionEncode i (⟨3,by omega⟩ : Fin A),j)) ∧
      AACFineGeometry.NonGrid (by omega) w ∧
      ¬AACMarkIntervals.IsMark hK turns (⟨2,by omega⟩ : Fin A) w := by
  have hA : 0<A := by omega
  have step (z : Nat) (hz : z+1<A) :
      successor (Nat.mul_pos hK hA) (AnchoredEmbedding.positionEncode i (⟨z,by omega⟩ : Fin A))=
        AnchoredEmbedding.positionEncode i (⟨z+1,hz⟩ : Fin A) := by
    apply Fin.ext
    have hi := i.isLt
    simp only [SquareLift.successor,AnchoredEmbedding.positionEncode]
    change (A*i.val+z+1)%(K*A)=A*i.val+(z+1)
    have hm := Nat.mul_le_mul_right A (show i.val+1≤K by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hm
    have hcomm : A*i.val=i.val*A := Nat.mul_comm _ _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp : predecessor (Nat.mul_pos hK hA)
      (AnchoredEmbedding.positionEncode i (⟨2,by omega⟩ : Fin A))=
      AnchoredEmbedding.positionEncode i (⟨1,by omega⟩ : Fin A) := by
    have ht := congrArg (predecessor (Nat.mul_pos hK hA)) (step 1 (by omega))
    rw [predecessor_successor] at ht
    exact ht.symm
  have hv : AACFineGeometry.NonGrid hA (AnchoredEmbedding.positionEncode i (⟨2,by omega⟩ : Fin A),j) := by
    apply (AACFineGeometry.nonGrid_iff hA _).mpr
    simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt (show 2<A by omega)]
    omega
  have hn := AACFineGeometry.nonGrid_neighbors hK hA hB hv hadj
  have hw : w=(AnchoredEmbedding.positionEncode i (⟨1,by omega⟩ : Fin A),j) ∨
      w=(AnchoredEmbedding.positionEncode i (⟨3,by omega⟩ : Fin A),j) := by
    rcases hn with hn|hn
    · exact Or.inr (hn.trans (Prod.ext (step 2 (by omega)) rfl))
    · exact Or.inl (hn.trans (Prod.ext hp rfl))
  refine ⟨hw,?_,?_⟩
  · apply (AACFineGeometry.nonGrid_iff hA _).mpr
    rcases hw with hw|hw <;> rw [hw]
    all_goals
      simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt (show 1<A by omega),
        Nat.mod_eq_of_lt (show 3<A by omega)]
      omega
  · rintro ⟨k,l,he,ht⟩
    have hr := congrArg (fun v : AACTransition.Fine K A B=>v.1.val%A) he
    rcases hw with hw|hw <;> rw [hw] at hr
    all_goals
      simp only [AnchoredEmbedding.positionEncode,Nat.mul_add_mod,Nat.mod_eq_of_lt (show 1<A by omega),
        Nat.mod_eq_of_lt (show 2<A by omega),Nat.mod_eq_of_lt (show 3<A by omega)] at hr
      omega

section Normalize
omit hr
variable {V : Type} {L : Nat}

def reorient (hL : 0<L) (F : Fin L→V) (start : Fin L) (eps : Bool) (n : Fin L) : V :=
  F (if eps then forward hL start n else backward hL start n)

theorem reorient_injective (hL : 0<L) (F : Fin L→V) (hF : Function.Injective F)
    (start : Fin L) (eps : Bool) : Function.Injective (reorient hL F start eps) := by
  intro n m he
  cases eps
  · exact backward_injective hL start (hF he)
  · exact forward_injective hL start (hF he)

theorem reorient_edge (hL : 0<L) (F : Fin L→V) (start : Fin L) (eps : Bool) (n : Fin L) :
    SameEdge (reorient hL F start eps n,reorient hL F start eps (successor hL n))
      (F (HamiltonOrient.edgeIndex hL start eps n),F (successor hL (HamiltonOrient.edgeIndex hL start eps n))) := by
  cases eps
  · change SameEdge (F (backward hL start n),F (backward hL start (successor hL n)))
      (F (backward hL start (successor hL n)),F (successor hL (backward hL start (successor hL n))))
    rw [OrientedClock.reverse_step]
    exact Or.inr rfl
  · change SameEdge (F (forward hL start n),F (forward hL start (successor hL n)))
      (F (forward hL start n),F (successor hL (forward hL start n)))
    rw [HamiltonNormalize.forward_successor]
    exact Or.inl rfl

/-- Literal recut/reversal at a displayed undirected edge. Its orientation
is obtained from the edge equality, not an existence of suitable tours. -/
theorem edge_normalization (h3 : 3≤L) (F : Fin L→V) (i : Fin L) (u v : V)
    (hi : SameEdge (F i,F (successor (by omega) i)) (u,v)) :
    ∃start eps, reorient (by omega) F start eps ⟨0,by omega⟩=u ∧
      reorient (by omega) F start eps ⟨1,by omega⟩=v := by
  have hf (start : Fin L) : forward (by omega) start ⟨1,by omega⟩=successor (by omega) start := rfl
  have hb (start : Fin L) : backward (by omega) (successor (by omega) start) ⟨1,by omega⟩=start := by
    have hzero : (⟨1,by omega⟩ : Fin L)=successor (by omega) ⟨0,by omega⟩ := by
      apply Fin.ext
      simp only [successor,Nat.zero_add,Nat.mod_eq_of_lt (show 1<L by omega)]
    rw [hzero]
    have ht := OrientedClock.reverse_step (show 0<L by omega) (successor (show 0<L by omega) start) (⟨0,by omega⟩ : Fin L)
    rw [backward_zero] at ht
    have hi := congrArg (predecessor (show 0<L by omega)) ht
    simpa only [predecessor_successor] using hi
  rcases hi with hi|hi
  · refine ⟨i,true,?_,?_⟩
    · simpa only [reorient,ite_true,forward_zero] using congrArg Prod.fst hi
    · simpa only [reorient,ite_true,hf] using congrArg Prod.snd hi
  · refine ⟨successor (by omega) i,false,?_,?_⟩
    · simpa only [reorient,Bool.false_eq_true,ite_false,backward_zero] using congrArg Prod.snd hi
    · simpa only [reorient,Bool.false_eq_true,ite_false,hb] using congrArg Prod.fst hi

/-- A completely constructive normalization step for actual displayed
cycle edges; both external-neighbor laws are then inherited literally. -/
theorem normalize_pair (h3 : 3≤L) (F : Bool→Fin L→V)
    (hinj : ∀c, Function.Injective (F c))
    (hunique : ∀c n d m, SameEdge (F c n,F c (successor (by omega) n))
      (F d m,F d (successor (by omega) m))→c=d ∧ n=m)
    (color : Bool) (u v w : V) (i j : Fin L)
    (hi : SameEdge (F color i,F color (successor (by omega) i)) (u,v))
    (hj : SameEdge (F (!color) j,F (!color) (successor (by omega) j)) (u,w))
    (hv : ∀n,F (!color) n≠v) (hw : ∀n,F color n≠w) :
    ∃(P : ForkTransfer.ForkPair V L) (s : Fin L) (a : Bool) (t : Fin L) (b : Bool),
      P.C=reorient (by omega) (F color) s a ∧ P.D=reorient (by omega) (F (!color)) t b := by
  obtain ⟨s,a,ha0,ha1⟩ := edge_normalization (r:=r) h3 (F color) i u v hi
  obtain ⟨t,b,hb0,hb1⟩ := edge_normalization (r:=r) h3 (F (!color)) j u w hj
  refine ⟨{
    large := h3
    C := reorient (by omega) (F color) s a
    D := reorient (by omega) (F (!color)) t b
    C_injective := reorient_injective _ _ (hinj color) s a
    D_injective := reorient_injective _ _ (hinj (!color)) t b
    anchor := ha0.trans hb0.symm
    D_outside := ?_
    C_outside := ?_
    disjoint := ?_
  },s,a,t,b,rfl,rfl⟩
  · intro n he
    rw [hb1] at he
    exact hw _ he.symm
  · intro n he
    rw [ha1] at he
    exact hv _ he.symm
  · intro n m he
    have hc := reorient_edge (show 0<L by omega) (F color) s a n
    have hd := reorient_edge (show 0<L by omega) (F (!color)) t b m
    have hh := hunique _ _ _ _ (sameEdge_trans (sameEdge_symm hc) (sameEdge_trans he hd))
    cases color <;> cases hh.1
/-- Recutting and reversing both outputs preserves their entire literal
undirected union, with actual old/new edge indices in both directions. -/
theorem normalized_union (h3 : 3≤L) (F : Bool→Fin L→V) (color : Bool)
    (P : ForkTransfer.ForkPair V L) (s : Fin L) (a : Bool) (t : Fin L) (b : Bool)
    (hC : P.C=reorient (by omega) (F color) s a)
    (hD : P.D=reorient (by omega) (F (!color)) t b) (u v : V) :
    P.unionRelation u v ↔ ∃c n,SameEdge (F c n,F c (successor (by omega) n)) (u,v) := by
  constructor
  · rintro ⟨label,he⟩
    cases label with
    | inl n =>
      change SameEdge (P.C n,P.C (successor P.positive n)) (u,v) at he
      rw [hC] at he
      exact ⟨color,HamiltonOrient.edgeIndex P.positive s a n,
        sameEdge_trans (sameEdge_symm (reorient_edge P.positive (F color) s a n)) he⟩
    | inr n =>
      change SameEdge (P.D n,P.D (successor P.positive n)) (u,v) at he
      rw [hD] at he
      exact ⟨!color,HamiltonOrient.edgeIndex P.positive t b n,
        sameEdge_trans (sameEdge_symm (reorient_edge P.positive (F (!color)) t b n)) he⟩
  · rintro ⟨c,n,he⟩
    by_cases hc : c=color
    · subst c
      obtain ⟨j,hj⟩ := HamiltonOrient.edgeIndex_surjective P.positive s a n
      refine ⟨Sum.inl j,?_⟩
      change SameEdge (P.C j,P.C (successor P.positive j)) (u,v)
      rw [hC]
      have hh := reorient_edge P.positive (F color) s a j
      rw [hj] at hh
      exact sameEdge_trans hh he
    · have hc' : c= !color := by cases c <;> cases color <;> simp_all
      subst c
      obtain ⟨j,hj⟩ := HamiltonOrient.edgeIndex_surjective P.positive t b n
      refine ⟨Sum.inr j,?_⟩
      change SameEdge (P.D j,P.D (successor P.positive j)) (u,v)
      rw [hD]
      have hh := reorient_edge P.positive (F (!color)) t b j
      rw [hj] at hh
      exact sameEdge_trans hh he

theorem edge_owner_from_exclusion (hL : 0<L) (F : Bool→Fin L→V) (color c : Bool)
    (v u : V) (i : Fin L) (he : SameEdge (F c i,F c (successor hL i)) (u,v))
    (hx : ∀n,F (!color) n≠v) : c=color := by
  have hv : F c i=v ∨ F c (successor hL i)=v := by
    rcases he with he|he
    · exact Or.inr (congrArg Prod.snd he)
    · exact Or.inl (congrArg Prod.fst he)
  cases color <;> cases c
  · rfl
  · rcases hv with hv|hv <;> exact False.elim (hx _ hv)
  · rcases hv with hv|hv <;> exact False.elim (hx _ hv)
  · rfl

end Normalize

/-- The actual numeric ragged fold with a buffered second mark supplies a
normalized fork pair. Exclusivity and edge owners are DERIVED from actual
base flags and the proved numeric edge ledger, not supplied by the caller. -/
theorem buffered_fork {E : Nat} (hE : 0<E) (h2 : 2≤r)
    (base : Fin E→Y) (colorWord : Fin E→Bool)
    (hcut : AACMarkIntervals.cyclicFlag hE colorWord ⟨0,hE⟩=true)
    (hmark : ∀n m,AACMarkIntervals.cyclicFlag hE colorWord n=true→base n=base m→n=m)
    (hcollision : ∀n m,base n=base m→n=m ∨ colorWord n≠colorWord m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE colorWord))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (AACMarkIntervals.cyclicFlag hE colorWord))→Bool)
    (hq : 0<Profile.cardinality (AACMarkIntervals.cyclicFlag hE colorWord))
    (hreturn : ∀c t,applyWord (word layers selectors c) (C.vertex (t,c))=C.vertex (successor hr t,c))
    (hedges : ∀n m,SameEdge (base n,base (successor hE n)) (base m,base (successor hE m))→n=m)
    (hcard : 3≤Profile.cardinality (AACMarkIntervals.cyclicFlag hE colorWord))
    (hleft : ∀(n : Fin E),n.val+1=(markIndex (AACMarkIntervals.cyclicFlag hE colorWord) ⟨1,by omega⟩).val→
      AACMarkIntervals.cyclicFlag hE colorWord n=false)
    (hright : ∀(n : Fin E),n.val=(markIndex (AACMarkIntervals.cyclicFlag hE colorWord) ⟨1,by omega⟩).val+1→
      AACMarkIntervals.cyclicFlag hE colorWord n=false)
    (hunique : ∀(n : Fin E),
      (n.val+1=(markIndex (AACMarkIntervals.cyclicFlag hE colorWord) ⟨1,by omega⟩).val ∨
       n.val=(markIndex (AACMarkIntervals.cyclicFlag hE colorWord) ⟨1,by omega⟩).val+1)→∀m,base m=base n→m=n)
    (hlarge : 3≤(AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length) (x : X) :
    ∃P : ForkTransfer.ForkPair (Y×X)
      (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length,
      ∀u v,P.unionRelation u v ↔ AACFoldEdgeLedger.HostAdjacent hE
        (AACMarkIntervals.cyclicFlag hE colorWord) base layers u v := by
  let S := AACMarkIntervals.cyclicFlag hE colorWord
  let F := fun c n=>foldVertex S base C layers selectors c (AACFoldClock.numeric S hq n)
  have hinj (c : Bool) : Function.Injective (F c) :=
    AACFoldClock.physical_injective hE hr base colorWord C layers selectors c hq hcut hmark hcollision
  have hp := AACFoldEdgeLedger.numeric_partition hE h2 S hcut base C layers selectors hq hreturn
    (fun j k he=>by
      have hm := hmark _ _ (markIndex_spec S j).1 he
      have hj := (markIndex_spec S j).2
      have hk := (markIndex_spec S k).2
      rw [hm] at hj
      exact Fin.ext (by omega)) hedges
  have huniq : ∀c n d m,SameEdge (F c n,F c (successor (AACFoldClock.length_pos hr S hq) n))
      (F d m,F d (successor (AACFoldClock.length_pos hr S hq) m))→c=d ∧ n=m := by
    intro c n d m he
    have hh := hp.2.1 (c,n) (d,m) he
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  obtain ⟨a,b,c,ha,hb,hma,hmb,hna,hnb⟩ := buffered_second_mark hE base colorWord hcut hmark hcollision
    C layers selectors hq hcard hleft hright hunique x
  let m := markIndex S (⟨1,by change 1<Profile.cardinality (AACMarkIntervals.cyclicFlag hE colorWord); omega⟩ : Fin (Profile.cardinality S))
  have hsa : successor hE a=m := by
    apply Fin.ext
    change (a.val+1)%E=m.val
    rw [ha,Nat.mod_eq_of_lt m.isLt]
  have hsb : successor hE m=b := by
    apply Fin.ext
    change (m.val+1)%E=b.val
    rw [←hb,Nat.mod_eq_of_lt b.isLt]
  have hea : AACFoldEdgeLedger.HostAdjacent hE S base layers (base m,x) (base a,x) := by
    refine ⟨Sum.inr (a,x),Or.inr ?_⟩
    simp only [AACFoldEdgeLedger.decode,hsa]
  have heb : AACFoldEdgeLedger.HostAdjacent hE S base layers (base m,x) (base b,x) := by
    refine ⟨Sum.inr (m,x),Or.inl ?_⟩
    simp only [AACFoldEdgeLedger.decode,hsb]
  obtain ⟨⟨ca,i⟩,hi⟩ := hp.1 _ _ hea
  obtain ⟨⟨cb,j⟩,hj⟩ := hp.1 _ _ heb
  have hca : ca=c := edge_owner_from_exclusion (AACFoldClock.length_pos hr S hq) F c ca (base a,x) (base m,x) i hi hna
  have hcb : cb= !c := edge_owner_from_exclusion (AACFoldClock.length_pos hr S hq) F (!c) cb (base b,x) (base m,x) j hj
    (by simpa only [Bool.not_not] using hnb)
  subst ca
  subst cb
  obtain ⟨P,s,eps,t,eta,hC,hD⟩ := normalize_pair (r:=r) hlarge F hinj huniq c (base m,x) (base a,x) (base b,x) i j hi hj hna hnb
  refine ⟨P,?_⟩
  intro u v
  rw [normalized_union (r:=r) hlarge F c P s eps t eta hC hD]
  constructor
  · rintro ⟨cc,n,he⟩
    obtain ⟨label,hl⟩ := hp.2.2 (cc,n)
    exact ⟨label,sameEdge_trans hl he⟩
  · intro hh
    obtain ⟨⟨cc,n⟩,he⟩ := hp.1 u v hh
    exact ⟨cc,n,he⟩

/-- At a literal isolated turn with A=2, the two nearest internal
neighbors of the grid are unmarked. Their incident base edges have opposite
ACTUAL colors, for any turn pattern and any row. -/
theorem isolated_two_neighbors {K B : Nat} (hK : 0<K)
    (turns : AACTransition.Grid K B→Bool) (i : Fin K) (j : Fin B)
    (hbefore : turns (predecessor hK i,j)≠turns (i,j))
    (hafter : turns (i,j)≠turns (successor hK i,j)) :
    ¬AACMarkIntervals.IsMark hK turns (⟨1,by decide⟩ : Fin 2)
      (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j) ∧
    ¬AACMarkIntervals.IsMark hK turns (⟨1,by decide⟩ : Fin 2)
      (AnchoredEmbedding.positionEncode i (⟨1,by decide⟩ : Fin 2),j) ∧
    AACMarkIntervals.edgeColor hK (by decide : 0<2) turns (⟨1,by decide⟩ : Fin 2)
      (Sum.inl (AnchoredEmbedding.positionEncode (predecessor hK i) (⟨1,by decide⟩ : Fin 2),j)) ≠
    AACMarkIntervals.edgeColor hK (by decide : 0<2) turns (⟨1,by decide⟩ : Fin 2)
      (Sum.inl (AnchoredEmbedding.positionEncode i (⟨0,by decide⟩ : Fin 2),j)) := by
  constructor
  · rw [AACMarkIntervals.mark_encode_iff hK (by decide : 0<2),successor_predecessor]
    exact fun h=>hbefore h.2
  constructor
  · rw [AACMarkIntervals.mark_encode_iff hK (by decide : 0<2)]
    exact fun h=>hafter h.2
  · rw [AACMarkIntervals.edgeColor_after hK (by decide : 0<2) turns
      (⟨1,by decide⟩ : Fin 2) (⟨1,by decide⟩ : Fin 2) (predecessor hK i) j (by decide),
      AACMarkIntervals.edgeColor_before hK (by decide : 0<2) turns
      (⟨1,by decide⟩ : Fin 2) (⟨0,by decide⟩ : Fin 2) i j (by decide)]
    unfold AACMarkIntervals.endColor AACMarkIntervals.startColor
    rw [successor_predecessor]
    cases hh : AACMarkIntervals.rowColor j <;> cases ht : turns (i,j) <;> simp [hh,ht]

/-- Actual chronological marks are exactly literal geometric marks; this
statement includes the final incoming cyclic edge. -/
theorem actual_flag_iff {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : AACTransition.Grid K B→Bool}
    (O : AACMerge.Orbit (AACTransition.State K B) (AACTransition.transition hK hB turns) N hN)
    (hE : (AACFine.indexList (A:=A) O).length=E) (hpos : 0<E)
    (z : Fin A) (hz : 0<z.val) (n : Fin E) :
    AACMarkIntervals.cyclicFlag hpos (AACMarkIntervals.numericColor hK hA hB O hE z) n=true ↔
      AACMarkIntervals.IsMark hK turns z (AACFineClock.fineVertex hK hA hB O hE n) := by
  have ht := AACMarkIntervals.numeric_change_iff hK hA hB hb O hE hpos z hz (predecessor hpos n)
  rw [successor_predecessor] at ht
  simpa only [AACMarkIntervals.cyclicFlag,decide_eq_true_eq] using ht

/-- Both actual cyclic neighbors of every buffered chronological mark are
unmarked and UNIQUE after genuine physical clock transport. This removes
neighbor flag/uniqueness inputs when instantiating the buffered fork. -/
theorem actual_buffered_neighbors {U V : Type} {K A B N E : Nat}
    (hK : 0<K) (hA4 : 4≤A) (hB : 0<B) (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0)
    {hN : 0<N} {turns : AACTransition.Grid K B→Bool}
    (O : AACMerge.Orbit (AACTransition.State K B) (AACTransition.transition hK hB turns) N hN)
    (hE : (AACFine.indexList (A:=A) O).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (AACFineClock.fineLabel hK (by omega) hB O hE))
    (G : SourceClock.ClockData U (K*A)) (H : SourceClock.ClockData V B)
    (n : Fin E)
    (hn : AACMarkIntervals.cyclicFlag hpos
      (AACMarkIntervals.numericColor hK (by omega) hB O hE (⟨2,by omega⟩ : Fin A)) n=true)
    (m : Fin E) (hm : m=successor hpos n ∨ m=predecessor hpos n) :
    AACMarkIntervals.cyclicFlag hpos
      (AACMarkIntervals.numericColor hK (by omega) hB O hE (⟨2,by omega⟩ : Fin A)) m=false ∧
    ∀p,AACFineGeometry.physical G H (AACFineClock.fineVertex hK (by omega) hB O hE p)=
      AACFineGeometry.physical G H (AACFineClock.fineVertex hK (by omega) hB O hE m)→p=m := by
  have hA : 0<A := by omega
  have hv := (actual_flag_iff hK hA hB hb O hE hpos (⟨2,by omega⟩ : Fin A) (show 0<2 by decide) n).mp hn
  obtain ⟨i,j,hv,ht⟩ := hv
  have adj : AACTransition.Adjacent hK hA hB
      (AnchoredEmbedding.positionEncode i (⟨2,by omega⟩ : Fin A),j)
      (AACFineClock.fineVertex hK hA hB O hE m) := by
    rcases hm with hm|hm
    · rw [hm,←hv]
      exact ⟨AACFineClock.fineLabel hK hA hB O hE n,AACFineClock.fineVertex_step hK hA hB O hE hpos n⟩
    · have he := AACFineClock.fineVertex_step hK hA hB O hE hpos (predecessor hpos n)
      rw [successor_predecessor,hv] at he
      refine ⟨AACFineClock.fineLabel hK hA hB O hE (predecessor hpos n),?_⟩
      rw [hm]
      exact sameEdge_trans he (Or.inr rfl)
  have hg := buffered_adjacent (r:=r) hK hA4 hB turns i j _ adj
  constructor
  · cases hf : AACMarkIntervals.cyclicFlag hpos
      (AACMarkIntervals.numericColor hK hA hB O hE (⟨2,by omega⟩ : Fin A)) m
    · rfl
    · exact False.elim (hg.2.2 ((actual_flag_iff hK hA hB hb O hE hpos
        (⟨2,by omega⟩ : Fin A) (show 0<2 by decide) m).mp hf))
  · intro p hp
    have he := AACFineGeometry.physical_injective G H hp
    exact (AACFineGeometry.nonGrid_clock_collision hK hA hB h3 hB3 O hE hpos hE2 hinj m p hg.2.1 he.symm).symm

#print axioms actual_flag_iff
#print axioms actual_buffered_neighbors
#print axioms isolated_two_neighbors
#print axioms normalized_union
#print axioms buffered_fork
#print axioms edge_normalization
#print axioms normalize_pair
#print axioms buffered_adjacent
#print axioms buffered_second_mark
#print axioms numeric_mark_common
#print axioms numeric_interior_mem_iff
#print axioms physical_internal_unique
#print axioms mark_common
#print axioms interior_mem_iff
#print axioms interior_exclusive
#print axioms opposite_interiors
end ErdePaths.AACFoldFork
