import ErdePaths.AACFoldGeometry
import ErdePaths.FiniteSaturation

namespace ErdePaths.AACFoldClock
open SquareLift SourceClock AACFoldOrder AACFoldGeometry

namespace Weighted
variable {N : Nat}
abbrev Position (w : Fin N→Nat) := (j : Fin N) × Fin (w j)

def next (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) (p : Position w) : Position w :=
  if hk : p.2.val+1<w p.1 then ⟨p.1,⟨p.2.val+1,hk⟩⟩
  else ⟨successor hN p.1,⟨0,hw _⟩⟩

def all (w : Fin N→Nat) : List (Position w) :=
  (List.finRange N).flatMap fun j => (List.finRange (w j)).map fun k => ⟨j,k⟩

theorem all_mem (w : Fin N→Nat) (p : Position w) : p∈all w := by
  rcases p with ⟨j,k⟩
  exact List.mem_flatMap.mpr ⟨j,List.mem_finRange j,List.mem_map.mpr ⟨k,List.mem_finRange k,rfl⟩⟩

theorem all_nodup (w : Fin N→Nat) : (all w).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j hj
    exact List.Pairwise.map _ (fun k l hne he => hne (Fin.ext (congrArg (fun p : Position w => p.2.val) he))) (List.nodup_finRange _)
  · apply (List.nodup_finRange N).imp
    intro j z hne x hx y hy he
    obtain ⟨k,hk,hx⟩ := List.mem_map.mp hx
    obtain ⟨l,hl,hy⟩ := List.mem_map.mp hy
    exact hne (congrArg Sigma.fst (hx.trans (he.trans hy.symm)))

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


def headAt (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) (n : Nat) : Position w :=
  ⟨⟨n%N,Nat.mod_lt _ hN⟩,⟨0,hw _⟩⟩

theorem headAt_row (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) (j : Fin N) :
    headAt hN w hw j.val=⟨j,⟨0,hw _⟩⟩ := by
  have he : (⟨j.val%N,Nat.mod_lt _ hN⟩ : Fin N)=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  exact congrArg (fun j : Fin N => (⟨j,⟨0,hw _⟩⟩ : Position w)) he

theorem all_form (w : Fin N→Nat) :
    all w=(List.ofFn (fun j => List.ofFn (fun k : Fin (w j) => (⟨j,k⟩ : Position w)))).flatten := by
  simp only [all,List.flatMap_def,List.finRange,List.map_ofFn,Function.comp_def]

theorem all_telescoping (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) :
    headAt hN w hw 0 :: (all w).map (next hN w hw)=all w++[headAt hN w hw 0] := by
  let b (j : Fin N) := List.ofFn (fun k : Fin (w j) => (⟨j,k⟩ : Position w))
  let h (j : Fin (N+1)) := headAt hN w hw j.val
  have hs (j : Fin N) : h j.castSucc :: (b j).map (next hN w hw)=(b j)++[h j.succ] := by
    have hl := block_telescoping (next hN w hw) (hw j)
      (fun k => (⟨j,k⟩ : Position w)) (headAt hN w hw (j.val+1)) (fun k => by
        unfold next
        split
        · rfl
        · have he : (⟨(j.val+1)%N,Nat.mod_lt _ hN⟩ : Fin N)=successor hN j := rfl
          exact congrArg (fun z : Fin N => (⟨z,⟨0,hw _⟩⟩ : Position w)) he.symm)
    change headAt hN w hw j.val :: _=_
    rw [headAt_row]
    exact hl
  have hl := blocks_telescoping (next hN w hw) N b h hs
  change headAt hN w hw 0 :: ((List.ofFn b).flatten).map (next hN w hw)=
    (List.ofFn b).flatten++[headAt hN w hw N] at hl
  rw [←all_form] at hl
  have he : headAt hN w hw N=headAt hN w hw 0 := by
    apply congrArg (fun j : Fin N => (⟨j,⟨0,hw _⟩⟩ : Position w))
    apply Fin.ext
    simp
  rw [he] at hl
  exact hl

theorem all_rotation (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) :
    (all w).map (next hN w hw)=(all w).tail++[headAt hN w hw 0] := by
  have hl := all_telescoping hN w hw
  have hm := all_mem w (headAt hN w hw 0)
  cases hx : all w with
  | nil => simp [hx] at hm
  | cons x xs =>
    rw [hx] at hl
    simp only [List.cons_append,List.cons.injEq] at hl
    exact hl.2

theorem all_head (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) :
    (all w)[0]?=some (headAt hN w hw 0) := by
  have hl := all_telescoping hN w hw
  have hm := all_mem w (headAt hN w hw 0)
  cases hx : all w with
  | nil => simp [hx] at hm
  | cons x xs =>
    rw [hx] at hl
    simp only [List.cons_append,List.cons.injEq] at hl
    exact congrArg some hl.1.symm

def numeric (w : Fin N→Nat) (n : Fin (all w).length) : Position w := (all w)[n.val]
theorem numeric_injective (w : Fin N→Nat) : Function.Injective (numeric w) := by
  intro n m he
  exact Fin.ext ((all_nodup w).eq_of_getElem_eq n.isLt m.isLt he)
theorem numeric_surjective (w : Fin N→Nat) : Function.Surjective (numeric w) := by
  intro p
  obtain ⟨n,hn,he⟩ := List.mem_iff_getElem.mp (all_mem w p)
  exact ⟨⟨n,hn⟩,he⟩
theorem all_positive (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) : 0<(all w).length :=
  List.length_pos_of_mem (all_mem w (headAt hN w hw 0))
theorem numeric_next (hN : 0<N) (w : Fin N→Nat) (hw : ∀j,0<w j) (n : Fin (all w).length) :
    next hN w hw (numeric w n)=numeric w (successor (all_positive hN w hw) n) :=
  list_successor (all w) _ (next hN w hw) (headAt hN w hw 0)
    (all_rotation hN w hw) (all_head hN w hw) n
noncomputable def inverse (w : Fin N→Nat) (p : Position w) : Fin (all w).length :=
  Classical.choose (numeric_surjective w p)
theorem numeric_inverse (w : Fin N→Nat) (p : Position w) : numeric w (inverse w p)=p :=
  Classical.choose_spec (numeric_surjective w p)
theorem inverse_numeric (w : Fin N→Nat) (n : Fin (all w).length) : inverse w (numeric w n)=n :=
  numeric_injective w (numeric_inverse w _)
end Weighted


variable {E r : Nat}
noncomputable def scalarWeight (hq : 0<Profile.cardinality (S : Fin E→Bool)) :
    Fin (r*(Profile.cardinality S*2))→Nat := fun j => foldWeight S (Wiggle.indexCoordinates hq j)

 theorem scalarWeight_pos (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (j : Fin (r*(Profile.cardinality S*2))) : 0<scalarWeight (r:=r) hq j := foldWeight_pos S _

noncomputable def unpack (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (p : Weighted.Position (scalarWeight (r:=r) hq)) : FoldPosition (r:=r) S :=
  ⟨Wiggle.indexCoordinates hq p.1,p.2⟩

theorem unpack_injective (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Function.Injective (unpack (r:=r) S hq) := by
  intro p z he
  have hj := congrArg Sigma.fst he
  have hj' := congrArg (Wiggle.coordinateIndex hq) hj
  simp only [unpack,Wiggle.coordinateIndex_reverse] at hj'
  rcases p with ⟨j,k⟩
  rcases z with ⟨l,b⟩
  change j=l at hj'
  subst l
  have hk : k=b := Fin.ext (congrArg (fun p : FoldPosition (r:=r) S => p.2.val) he)
  subst b
  rfl

theorem unpack_surjective (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Function.Surjective (unpack (r:=r) S hq) := by
  intro p
  let j := Wiggle.coordinateIndex hq p.1
  have hj : Wiggle.indexCoordinates hq j=p.1 := Wiggle.coordinateIndex_inverse hq p.1
  let k : Fin (scalarWeight hq j) := ⟨p.2.val,by
    simp only [scalarWeight,hj]
    exact p.2.isLt⟩
  refine ⟨⟨j,k⟩,?_⟩
  apply foldPosition_ext S
  · exact congrArg Prod.fst hj
  · exact congrArg (fun x => x.2.1) hj
  · exact congrArg (fun x => x.2.2.val) hj
  · rfl

theorem unpack_next (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (p : Weighted.Position (scalarWeight (r:=r) hq)) :
    unpack S hq (Weighted.next (Nat.mul_pos hr (by omega)) (scalarWeight hq) (scalarWeight_pos S hq) p)=
      foldNext hr S hq (unpack S hq p) := by
  by_cases hn : p.2.val+1<scalarWeight hq p.1
  · have hn' : (unpack S hq p).2.val+1<foldWeight S (unpack S hq p).1 := hn
    rw [Weighted.next,dite_eq_left hn,foldNext,dite_eq_left hn']
    rfl
  · have hn' : ¬(unpack S hq p).2.val+1<foldWeight S (unpack S hq p).1 := hn
    rw [Weighted.next,dite_eq_right hn,foldNext,dite_eq_right hn']
    apply foldPosition_ext S
    · exact congrArg Prod.fst (Wiggle.indexCoordinates_next hr hq p.1)
    · exact congrArg (fun x => x.2.1) (Wiggle.indexCoordinates_next hr hq p.1)
    · exact congrArg (fun x => x.2.2.val) (Wiggle.indexCoordinates_next hr hq p.1)
    · rfl

noncomputable def all (S : Fin E→Bool) (hq : 0<Profile.cardinality S) : List (FoldPosition (r:=r) S) :=
  (Weighted.all (scalarWeight hq)).map (unpack S hq)

theorem all_nodup (S : Fin E→Bool) (hq : 0<Profile.cardinality S) : (all (r:=r) S hq).Nodup :=
  List.Pairwise.map _ (fun _ _ hne he => hne (unpack_injective S hq he)) (Weighted.all_nodup _)

theorem all_mem (S : Fin E→Bool) (hq : 0<Profile.cardinality S) (p : FoldPosition (r:=r) S) :
    p∈all S hq := by
  obtain ⟨z,hz⟩ := unpack_surjective S hq p
  exact List.mem_map.mpr ⟨z,Weighted.all_mem _ z,hz⟩

noncomputable def numeric (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length) : FoldPosition (r:=r) S :=
  unpack S hq (Weighted.numeric (scalarWeight hq) n)

theorem numeric_injective (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Function.Injective (numeric (r:=r) S hq) :=
  fun _ _ he => Weighted.numeric_injective _ (unpack_injective S hq he)

theorem numeric_surjective (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Function.Surjective (numeric (r:=r) S hq) := by
  intro p
  obtain ⟨z,hz⟩ := unpack_surjective S hq p
  obtain ⟨n,hn⟩ := Weighted.numeric_surjective (scalarWeight hq) z
  exact ⟨n,by unfold numeric; rw [hn,hz]⟩

noncomputable def inverse (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) : Fin (Weighted.all (scalarWeight (r:=r) hq)).length :=
  Classical.choose (numeric_surjective S hq p)

theorem numeric_inverse (S : Fin E→Bool) (hq : 0<Profile.cardinality S) (p : FoldPosition (r:=r) S) :
    numeric S hq (inverse S hq p)=p := Classical.choose_spec (numeric_surjective S hq p)

theorem inverse_numeric (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length) : inverse S hq (numeric S hq n)=n :=
  numeric_injective S hq (numeric_inverse S hq _)

theorem length_pos (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    0<(Weighted.all (scalarWeight (r:=r) hq)).length :=
  Weighted.all_positive (Nat.mul_pos hr (by omega)) _ (scalarWeight_pos S hq)

theorem numeric_next (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length) :
    numeric S hq (successor (length_pos hr S hq) n)=foldNext hr S hq (numeric S hq n) := by
  unfold numeric
  rw [←Weighted.numeric_next (Nat.mul_pos hr (by omega)) _ (scalarWeight_pos S hq)]
  exact unpack_next hr S hq _

/-- The actual ragged coordinates now have a complete scalar cyclic inverse. -/
noncomputable def clock (_hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    ClockData (FoldPosition (r:=r) S) (Weighted.all (scalarWeight (r:=r) hq)).length where
  cycle := numeric S hq
  position := inverse S hq
  position_cycle := inverse_numeric S hq
  cycle_position := numeric_inverse S hq


noncomputable def countCode (S : Fin E→Bool) (_hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) : Fin r × (Fin (Profile.cardinality S) ⊕ Fin E) :=
  (p.1.1,if hb : p.1.2.2.val=0 then .inl p.1.2.1 else
    .inr (gapIndex S ⟨p.1.2.1,⟨p.2.val,by simpa only [foldWeight,ite_false,hb] using p.2.isLt⟩⟩))

theorem countCode_injective (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Function.Injective (countCode (r:=r) S hq) := by
  intro p z he
  have ht := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  by_cases hp : p.1.2.2.val=0
  · by_cases hz : z.1.2.2.val=0
    · simp only [countCode,dite_eq_left hp,dite_eq_left hz,Sum.inl.injEq] at hi
      have hk : p.2.val=0 := by have hh := p.2.isLt; simp only [foldWeight,hp,ite_true] at hh; omega
      have hl : z.2.val=0 := by have hh := z.2.isLt; simp only [foldWeight,hz,ite_true] at hh; omega
      exact foldPosition_ext S p z ht hi (by omega) (by omega)
    · simp [countCode,hp,hz] at hi
  · by_cases hz : z.1.2.2.val=0
    · simp [countCode,hp,hz] at hi
    · simp only [countCode,dite_eq_right hp,dite_eq_right hz,Sum.inr.injEq] at hi
      have hg := gapIndex_injective S hi
      have hj := congrArg Sigma.fst hg
      have hk := congrArg (fun o => o.2.val) hg
      exact foldPosition_ext S p z ht hj (by have := p.1.2.2.isLt; have := z.1.2.2.isLt; omega) hk

theorem countCode_surjective (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (hq : 0<Profile.cardinality S) : Function.Surjective (countCode (r:=r) S hq) := by
  rintro ⟨t,z⟩
  cases z with
  | inl j =>
    let p : FoldPosition (r:=r) S := ⟨(t,j,⟨0,by decide⟩),⟨0,by simp [foldWeight]⟩⟩
    exact ⟨p,rfl⟩
  | inr n =>
    obtain ⟨⟨j,k⟩,hk⟩ := gapIndex_surjective hE S hzero n
    let p : FoldPosition (r:=r) S := ⟨(t,j,⟨1,by decide⟩),⟨k.val,by simp [foldWeight]⟩⟩
    refine ⟨p,?_⟩
    apply Prod.ext
    · rfl
    · simpa only [countCode,p,show ¬(1:Nat)=0 by decide,dite_false] using congrArg Sum.inr hk

variable {q : Nat}
def countFin (x : Fin r × (Fin q ⊕ Fin E)) : Fin (r*(q+E)) :=
  AnchoredEmbedding.positionEncode x.1 (match x.2 with
    | .inl j => ⟨j.val,by have := j.isLt; omega⟩
    | .inr n => ⟨q+n.val,by have := n.isLt; omega⟩)

theorem countFin_injective : Function.Injective (@countFin E r q) := by
  intro x z he
  by_cases hqe : 0<q+E
  · unfold countFin at he
    have hp := congrArg (AnchoredEmbedding.positionDecode hqe) he
    rw [AnchoredEmbedding.positionDecode_encode,AnchoredEmbedding.positionDecode_encode] at hp
    have ht := congrArg Prod.fst hp
    have hv := congrArg (fun p : Fin r × Fin (q+E) => p.2.val) hp
    rcases x with ⟨t,x⟩
    rcases z with ⟨u,z⟩
    change t=u at ht
    apply Prod.ext ht
    cases x <;> cases z <;> dsimp only at hv
    · apply congrArg Sum.inl; apply Fin.ext; exact hv
    · have := ‹Fin q›.isLt; omega
    · have := ‹Fin q›.isLt; omega
    · apply congrArg Sum.inr; apply Fin.ext; omega
  · rcases x.2 with j|n
    · have := j.isLt; omega
    · have := n.isLt; omega

theorem countFin_surjective (hq : 0<q) : Function.Surjective (@countFin E r q) := by
  intro n
  let p := AnchoredEmbedding.positionDecode (show 0<q+E by omega) n
  by_cases hp : p.2.val<q
  · refine ⟨(p.1,.inl ⟨p.2.val,hp⟩),?_⟩
    exact AnchoredEmbedding.positionEncode_decode (show 0<q+E by omega) n
  · refine ⟨(p.1,.inr ⟨p.2.val-q,by have := p.2.isLt; omega⟩),?_⟩
    have he : (⟨q+(p.2.val-q),by have := p.2.isLt; omega⟩ : Fin (q+E))=p.2 := Fin.ext (by change q+(p.2.val-q)=p.2.val; omega)
    change AnchoredEmbedding.positionEncode p.1 ⟨q+(p.2.val-q),_⟩=n
    rw [he]
    exact AnchoredEmbedding.positionEncode_decode (show 0<q+E by omega) n

private theorem finite_size {M N : Nat} (f : Fin M→Fin N)
    (hinj : Function.Injective f) (hsur : Function.Surjective f) : M=N := by
  have hm : ((List.finRange M).map f).Nodup :=
    List.Pairwise.map _ (fun _ _ hne he => hne (hinj he)) (List.nodup_finRange M)
  have hsub : (List.finRange M).map f ⊆ List.finRange N := by intro n _; exact List.mem_finRange n
  have hsub' : List.finRange N ⊆ (List.finRange M).map f := by
    intro n _
    obtain ⟨m,hm⟩ := hsur n
    exact List.mem_map.mpr ⟨m,List.mem_finRange m,hm⟩
  have hl := hm.length_le_of_subset hsub
  have hr := (List.nodup_finRange N).length_le_of_subset hsub'
  simp only [List.length_map,List.length_finRange] at hl hr
  omega

/-- Exact full ragged length: one arrival J edge per mark and one departure
base edge per actual fine Euler occurrence, at each turn. -/
theorem length_eq (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (hq : 0<Profile.cardinality S) :
    (Weighted.all (scalarWeight (r:=r) hq)).length=r*(E+Profile.cardinality S) := by
  let f := fun n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length =>
    countFin (countCode S hq (numeric S hq n))
  have hinj : Function.Injective f := fun _ _ he =>
    numeric_injective S hq (countCode_injective S hq (countFin_injective he))
  have hsur : Function.Surjective f := by
    intro n
    obtain ⟨c,hc⟩ := countFin_surjective hq n
    obtain ⟨p,hp⟩ := countCode_surjective hE S hzero hq c
    obtain ⟨m,hm⟩ := numeric_surjective S hq p
    exact ⟨m,by dsimp only [f]; rw [hm,hp,hc]⟩
  have hh := finite_size f hinj hsur
  simpa only [Nat.add_comm] using hh



/-- The scalar order is one actual orbit, with no hidden component choice. -/
theorem numeric_repeat (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) (n : Nat) :
    Nat.repeat (foldNext hr S hq) n (numeric S hq ⟨0,length_pos hr S hq⟩)=
      numeric S hq ⟨n%(Weighted.all (scalarWeight (r:=r) hq)).length,
        Nat.mod_lt _ (length_pos hr S hq)⟩ := by
  induction n with
  | zero => simp only [Nat.repeat,Nat.zero_mod]
  | succ n ih =>
    rw [Nat.repeat,ih,←numeric_next]
    congr 1
    apply Fin.ext
    simp only [successor,Nat.add_mod,Nat.mod_mod]

theorem single_orbit (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (p : FoldPosition (r:=r) S) :
    ∃n, n<(Weighted.all (scalarWeight (r:=r) hq)).length ∧
      Nat.repeat (foldNext hr S hq) n (numeric S hq ⟨0,length_pos hr S hq⟩)=p := by
  obtain ⟨n,hn⟩ := numeric_surjective S hq p
  refine ⟨n.val,n.isLt,?_⟩
  rw [numeric_repeat]
  simpa only [Nat.mod_eq_of_lt n.isLt] using hn

noncomputable def orbit (hr : 0<r) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    AACMerge.Orbit (FoldPosition (r:=r) S) (foldNext hr S hq)
      (Weighted.all (scalarWeight (r:=r) hq)).length (length_pos hr S hq) where
  point := numeric S hq
  injective := numeric_injective S hq
  next n := (numeric_next hr S hq n).symm

/-- An actual marked cut proves that the mark carrier is nonempty. -/
theorem cardinality_pos (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true) :
    0<Profile.cardinality S := by
  have hp : Profile.prefixCount S 1=1 := by
    simp only [Profile.prefixCount,Profile.indicator,dite_eq_left hE,hzero,Bool.toNat_true,Nat.zero_add]
  have hm := AACIntervalSplit.prefix_mono S (show 1≤E by omega)
  rw [hp] at hm
  exact Nat.lt_of_lt_of_le (by decide) hm

section Physical
open PairedLayers LayerPartition AACMarkIntervals
variable {Y X : Type} {Q : Y→Y→Prop} {R : X→X→Prop} {χ : X→Bool}
variable (hE : 0<E) (hr : 0<r) (base : Fin E→Y) (baseColor : Fin E→Bool)
variable (C : CycleData X R χ r hr)
variable (layers : Fin (Profile.cardinality (cyclicFlag hE baseColor))→CycleData X R χ r hr)
variable (selectors : Fin (Profile.cardinality (cyclicFlag hE baseColor))→Bool) (color : Bool)
variable (hq : 0<Profile.cardinality (cyclicFlag hE baseColor))

/-- The literal ambient cyclic vertex list, without a spanning-ambient claim. -/
noncomputable def physical (n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length) : Y×X :=
  foldVertex (cyclicFlag hE baseColor) base C layers selectors color (numeric (cyclicFlag hE baseColor) hq n)


theorem physical_injective (hcut : (cyclicFlag hE baseColor) ⟨0,hE⟩=true)
    (hmark : ∀n m, (cyclicFlag hE baseColor) n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m) :
    Function.Injective (physical hE hr base baseColor C layers selectors color hq) := by
  intro n m he
  exact numeric_injective (cyclicFlag hE baseColor) hq
    (foldVertex_injective hE base baseColor hcut hmark hcollision C layers selectors color he)

theorem physical_adjacent (hcut : (cyclicFlag hE baseColor) ⟨0,hE⟩=true)
    (hbase : ∀n, Q (base n) (base (successor hE n)))
    (hR : ∀u v, R u v→R v u)
    (hreturn : ∀t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) (n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length) :
    AnchoredEmbedding.ProductRelation Q R
      (physical hE hr base baseColor C layers selectors color hq n)
      (physical hE hr base baseColor C layers selectors color hq (successor (length_pos hr (cyclicFlag hE baseColor) hq) n)) := by
  unfold physical
  rw [numeric_next]
  exact foldVertex_step hE (cyclicFlag hE baseColor) hcut base hbase C layers selectors color hR hq hreturn _

/-- Actual output vertices, defined as the literal cyclic image. Coverage of
this subtype is constructed, not postulated for the ambient product. -/
abbrev Image := {v : Y×X // ∃n : Fin (Weighted.all (scalarWeight (r:=r) hq)).length,
  physical hE hr base baseColor C layers selectors color hq n=v}

/-- A genuine simple cyclic clock on its actual physical output vertices.
The graph relation is the restriction of the literal Cartesian relation. -/
noncomputable def cycle (hcut : (cyclicFlag hE baseColor) ⟨0,hE⟩=true)
    (hmark : ∀n m, (cyclicFlag hE baseColor) n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m)
    (hbase : ∀n, Q (base n) (base (successor hE n)))
    (hR : ∀u v, R u v→R v u)
    (hreturn : ∀t, applyWord (word layers selectors color) (C.vertex (t,color))=
      C.vertex (successor hr t,color)) :
    HamiltonData.CycleData (Image hE hr base baseColor C layers selectors color hq)
      (fun u v => AnchoredEmbedding.ProductRelation Q R u.val v.val) (Weighted.all (scalarWeight (r:=r) hq)).length (length_pos hr (cyclicFlag hE baseColor) hq) where
  cycle n := ⟨physical hE hr base baseColor C layers selectors color hq n,⟨n,rfl⟩⟩
  position v := Classical.choose v.property
  position_cycle n := physical_injective hE hr base baseColor C layers selectors color hq hcut hmark hcollision
    (Classical.choose_spec (show ∃m : Fin (Weighted.all (scalarWeight (r:=r) hq)).length,
      physical hE hr base baseColor C layers selectors color hq m=
        physical hE hr base baseColor C layers selectors color hq n from ⟨n,rfl⟩))
  cycle_position v := Subtype.ext (Classical.choose_spec v.property)
  adjacent n := physical_adjacent hE hr base baseColor C layers selectors color hq hcut hbase hR hreturn n

noncomputable def physicalList : List (Y×X) :=
  List.ofFn (physical hE hr base baseColor C layers selectors color hq)

theorem physicalList_nodup (hcut : (cyclicFlag hE baseColor) ⟨0,hE⟩=true)
    (hmark : ∀n m, (cyclicFlag hE baseColor) n=true→base n=base m→n=m)
    (hcollision : ∀n m, base n=base m→n=m ∨ baseColor n≠baseColor m) :
    (physicalList hE hr base baseColor C layers selectors color hq).Nodup :=
  FiniteSaturation.ofFn_nodup _ (physical_injective hE hr base baseColor C layers selectors color hq hcut hmark hcollision)

theorem physicalList_length (hcut : (cyclicFlag hE baseColor) ⟨0,hE⟩=true) :
    (physicalList hE hr base baseColor C layers selectors color hq).length=
      r*(E+Profile.cardinality (cyclicFlag hE baseColor)) := by
  rw [physicalList,List.length_ofFn]
  exact length_eq hE _ hcut hq
end Physical

#print axioms single_orbit
#print axioms orbit
#print axioms physicalList_nodup
#print axioms physicalList_length
#print axioms physical_adjacent
#print axioms physical_injective
#print axioms cycle
#print axioms length_eq
#print axioms numeric_next
#print axioms clock
end ErdePaths.AACFoldClock
