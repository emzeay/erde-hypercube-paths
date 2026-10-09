import ErdePaths.AACInduction
import ErdePaths.AACMarkIntervals

namespace ErdePaths.AACMarkExchange
open SquareLift AACTransition AACInduction AACMarkIntervals

theorem successor_zero {K : Nat} (hK : 1<K) :
    successor (by omega) (⟨0,by omega⟩ : Fin K)=⟨1,hK⟩ := by
  apply Fin.ext
  simp [successor,Nat.mod_eq_of_lt hK]

theorem successor_eq_zero {K : Nat} (hK : 0<K) (i : Fin K) :
    successor hK i=⟨0,hK⟩ ↔ i=predecessor hK ⟨0,hK⟩ := by
  constructor
  · intro hi
    have hh := congrArg (predecessor hK) hi
    simpa only [predecessor_successor] using hh
  · intro hi; rw [hi,successor_predecessor]

/-- A flipped row deletes agreement 0 and creates agreement -1, exactly. -/
theorem agreement_after {K B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (i : Fin K) (j : Fin B) :
    turnsAfter (by omega) t n (i,j)=turnsAfter (by omega) t n (successor (by omega) i,j) ↔
    (t i=t (successor (by omega) i) ∧ ¬(i=⟨0,by omega⟩ ∧ j.val<n)) ∨
      (i=predecessor (by omega) ⟨0,by omega⟩ ∧ j.val<n) := by
  have hpos : 0<K := by omega
  have hzero_ne : (⟨0,hpos⟩ : Fin K)≠predecessor hpos ⟨0,hpos⟩ := by
    intro he
    have hh := congrArg (successor hpos) he
    rw [successor_zero hK,successor_predecessor] at hh
    have hv := congrArg Fin.val hh
    change 1=0 at hv
    omega
  by_cases hr : j.val<n
  · by_cases hi : i=⟨0,hpos⟩
    · subst i
      have h1 : (⟨1,hK⟩ : Fin K)≠⟨0,hpos⟩ := by
        intro he
        have hv := congrArg Fin.val he
        change 1=0 at hv
        omega
      simp [turnsAfter,successor_zero hK,ht0,ht1,hr,h1,hzero_ne]
    · by_cases hp : i=predecessor hpos ⟨0,hpos⟩
      · subst i
        simp [turnsAfter,successor_predecessor,hi,hr,htlast,ht0]
      · have hs : successor hpos i≠⟨0,hpos⟩ := fun he => hp ((successor_eq_zero hpos i).mp he)
        simp [turnsAfter,hi,hs,hr,hp]
  · simp [turnsAfter,hr]

/-- Injectivity of the actual physical fixed-threshold points. -/
theorem point_injective {K A B : Nat} (z : Fin A) :
    Function.Injective (fun p : Fin K×Fin B => (AnchoredEmbedding.positionEncode p.1 z,p.2)) := by
  intro p q he
  have ha : 0<A := by have := z.isLt; omega
  have hi := congrArg (AnchoredEmbedding.positionDecode ha) (congrArg Prod.fst he)
  simp only [AnchoredEmbedding.positionDecode_encode] at hi
  have hip : p.1=q.1 := congrArg (fun x : Fin K×Fin A => x.1) hi
  have hjp : p.2=q.2 := congrArg (fun x : Fin (K*A)×Fin B => x.2) he
  exact Prod.ext hip hjp

theorem mark_point_iff {K A B : Nat} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A)
    (i : Fin K) (j : Fin B) :
    IsMark hK turns z (AnchoredEmbedding.positionEncode i z,j) ↔
      turns (i,j)=turns (successor hK i,j) := by
  constructor
  · rintro ⟨i',j',he,hh⟩
    have hp := @point_injective K A B z (i,j) (i',j') he
    rcases Prod.mk.inj hp with ⟨hi,hj⟩
    subst i'; subst j'
    exact hh
  · intro hh; exact ⟨i,j,rfl,hh⟩

/-- Exact actual IsMark formula at every fine vertex, before any ordering of
marks or their traversal occurrences is chosen. -/
theorem marks_after {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (v : Fine K A B) :
    IsMark (by omega) (turnsAfter (by omega) t n) z v ↔
    ∃i : Fin K, ∃j : Fin B, v=(AnchoredEmbedding.positionEncode i z,j) ∧
      ((t i=t (successor (by omega) i) ∧ ¬(i=⟨0,by omega⟩ ∧ j.val<n)) ∨
       (i=predecessor (by omega) ⟨0,by omega⟩ ∧ j.val<n)) := by
  unfold IsMark
  constructor
  · rintro ⟨i,j,hv,hm⟩
    exact ⟨i,j,hv,(agreement_after hK t ht0 ht1 htlast n i j).mp hm⟩
  · rintro ⟨i,j,hv,hm⟩
    exact ⟨i,j,hv,(agreement_after hK t ht0 ht1 htlast n i j).mpr hm⟩

def Removed {K A B : Nat} (hK : 0<K) (n : Nat) (z : Fin A) (v : Fine K A B) : Prop :=
  ∃j : Fin B, j.val<n ∧ v=(AnchoredEmbedding.positionEncode ⟨0,hK⟩ z,j)

def Added {K A B : Nat} (hK : 0<K) (n : Nat) (z : Fin A) (v : Fine K A B) : Prop :=
  ∃j : Fin B, j.val<n ∧ v=(AnchoredEmbedding.positionEncode (predecessor hK ⟨0,hK⟩) z,j)

/-- Literal physical set substitution: exactly Removed is deleted and Added
is inserted. No post-flip count or preservation premise is used. -/
theorem mark_substitution {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (v : Fine K A B) :
    IsMark (by omega) (turnsAfter (by omega) t n) z v ↔
    (IsMark (by omega) (fun g => t g.1) z v ∧ ¬Removed (by omega) n z v) ∨ Added (by omega) n z v := by
  rw [marks_after hK t ht0 ht1 htlast]
  constructor
  · rintro ⟨i,j,hv,hh⟩
    rcases hh with ⟨hm,hnot⟩|⟨hi,hj⟩
    · left
      refine ⟨⟨i,j,hv,hm⟩,?_⟩
      rintro ⟨j',hj',hv'⟩
      have hp := @point_injective K A B z (i,j) (⟨0,by omega⟩,j') (hv.symm.trans hv')
      rcases Prod.mk.inj hp with ⟨hi,hj⟩
      apply hnot
      exact ⟨hi,by rw [hj]; exact hj'⟩
    · right; exact ⟨j,hj,by rw [hv,hi]⟩
  · intro hh
    rcases hh with ⟨⟨i,j,hv,hm⟩,hnot⟩|⟨j,hj,hv⟩
    · refine ⟨i,j,hv,Or.inl ⟨hm,?_⟩⟩
      rintro ⟨hi,hj⟩
      exact hnot ⟨j,hj,by rw [hv,hi]⟩
    · exact ⟨predecessor (by omega) ⟨0,by omega⟩,j,hv,Or.inr ⟨rfl,hj⟩⟩

/-- Away from the two exchanged physical endpoint sets, marks are literally
unchanged; this applies in particular to every unflipped row. -/
theorem unchanged {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (v : Fine K A B)
    (hr : ¬Removed (by omega) n z v) (ha : ¬Added (by omega) n z v) :
    IsMark (by omega) (turnsAfter (by omega) t n) z v ↔ IsMark (by omega) (fun g => t g.1) z v := by
  rw [mark_substitution hK t ht0 ht1 htlast]
  simp only [hr,ha,not_false_eq_true,and_true,or_false]

theorem removed_is_mark {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (n : Nat) (z : Fin A) (v : Fine K A B) (hr : Removed (by omega) n z v) :
    IsMark (by omega) (fun g => t g.1) z v := by
  obtain ⟨j,hj,rfl⟩ := hr
  rw [mark_point_iff,successor_zero hK,ht0,ht1]

theorem added_not_mark {K A B : Nat} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (v : Fine K A B) (ha : Added (by omega) n z v) :
    ¬IsMark (by omega) (fun g => t g.1) z v := by
  obtain ⟨j,hj,rfl⟩ := ha
  rw [mark_point_iff,successor_predecessor,htlast,ht0]
  decide

/-- Physical image of an explicit fine-grid vertex predicate. -/
def ImageSet {X U : Type} (f : X→U) (P : X→Prop) (v : U) : Prop :=
  ∃x, f x=v ∧ P x

private theorem image_substitution {X U : Type} (f : X→U) (hf : Function.Injective f)
    (P R A Q : X→Prop) (hq : ∀x, Q x↔(P x∧¬R x)∨A x) (v : U) :
    ImageSet f Q v ↔ (ImageSet f P v∧¬ImageSet f R v)∨ImageSet f A v := by
  constructor
  · rintro ⟨x,hx,hqx⟩
    rcases (hq x).mp hqx with ⟨hp,hr⟩|ha
    · left; refine ⟨⟨x,hx,hp⟩,?_⟩
      rintro ⟨y,hy,hyR⟩
      have he : y=x := hf (hy.trans hx.symm)
      exact hr (he ▸ hyR)
    · exact Or.inr ⟨x,hx,ha⟩
  · rintro (⟨⟨x,hx,hp⟩,hr⟩|⟨x,hx,ha⟩)
    · exact ⟨x,hx,(hq x).mpr (Or.inl ⟨hp,fun hxR => hr ⟨x,hx,hxR⟩⟩)⟩
    · exact ⟨x,hx,(hq x).mpr (Or.inr ha)⟩

/-- Exact substitution after transport along an actual injective host map. -/
theorem physical_substitution {K A B : Nat} {U : Type} (hK : 1<K)
    (t : Fin K→Bool) (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (f : Fine K A B→U) (hf : Function.Injective f) (v : U) :
    ImageSet f (IsMark (by omega) (turnsAfter (by omega) t n) z) v ↔
    (ImageSet f (IsMark (by omega) (fun g => t g.1) z) v ∧
      ¬ImageSet f (Removed (by omega) n z) v) ∨ ImageSet f (Added (by omega) n z) v :=
  image_substitution f hf _ _ _ _ (mark_substitution hK t ht0 ht1 htlast n z) v

attribute [local instance] Classical.propDecidable
/-- Physical mark multiplicity as a literal 0/1 incidence. -/
noncomputable def incidence (P : Prop) : Nat := if P then 1 else 0

private theorem reciprocal_count (P P' R A Q Q' : Prop)
    (hq : Q↔(P∧¬R)∨A) (hq' : Q'↔(P'∧¬A)∨R)
    (hr : R→P) (ha : A→¬P) (hr' : A→P') (ha' : R→¬P') :
    incidence Q+incidence Q'=incidence P+incidence P' := by
  by_cases hR : R
  · have hP := hr hR
    have hP' := ha' hR
    have hA : ¬A := fun hh => ha hh hP
    simp [incidence,hq,hq',hR,hP,hP',hA]
  · by_cases hA : A
    · have hP := ha hA
      have hP' := hr' hA
      simp [incidence,hq,hq',hR,hP,hP',hA]
    · simp [incidence,hq,hq',hR,hA]

private theorem image_removed_added {K A B : Nat} {U : Type} (hK : 0<K)
    (n : Nat) (z : Fin A) (f g : Fine K A B→U)
    (he : ∀j : Fin B, f (AnchoredEmbedding.positionEncode ⟨0,hK⟩ z,j)=
      g (AnchoredEmbedding.positionEncode (predecessor hK ⟨0,hK⟩) z,j)) (v : U) :
    ImageSet f (Removed hK n z) v ↔ ImageSet g (Added hK n z) v := by
  constructor
  · rintro ⟨x,hx,j,hj,hpoint⟩
    subst x
    refine ⟨(AnchoredEmbedding.positionEncode (predecessor hK ⟨0,hK⟩) z,j),?_,j,hj,rfl⟩
    exact (he j).symm.trans hx
  · rintro ⟨x,hx,j,hj,hpoint⟩
    subst x
    refine ⟨(AnchoredEmbedding.positionEncode ⟨0,hK⟩ z,j),?_,j,hj,rfl⟩
    exact (he j).trans hx

/-- Two actual embedded AACs with reciprocal physical exchanged endpoints
preserve their aggregate pointwise mark multiplicity. The only pairing input
is equality of the concrete endpoint vertices, not a count-preservation oracle. -/
theorem reciprocal_preservation {K A B : Nat} {U : Type} (hK : 1<K)
    (t t' : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (ht0' : t' ⟨0,by omega⟩=false) (ht1' : t' ⟨1,hK⟩=false)
    (htlast' : t' (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (f g : Fine K A B→U)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (he0 : ∀j : Fin B, f (AnchoredEmbedding.positionEncode ⟨0,by omega⟩ z,j)=
      g (AnchoredEmbedding.positionEncode (predecessor (by omega) ⟨0,by omega⟩) z,j))
    (he1 : ∀j : Fin B, g (AnchoredEmbedding.positionEncode ⟨0,by omega⟩ z,j)=
      f (AnchoredEmbedding.positionEncode (predecessor (by omega) ⟨0,by omega⟩) z,j))
    (v : U) :
    incidence (ImageSet f (IsMark (by omega) (turnsAfter (by omega) t n) z) v)+
      incidence (ImageSet g (IsMark (by omega) (turnsAfter (by omega) t' n) z) v)=
    incidence (ImageSet f (IsMark (by omega) (fun w => t w.1) z) v)+
      incidence (ImageSet g (IsMark (by omega) (fun w => t' w.1) z) v) := by
  have hq := physical_substitution hK t ht0 ht1 htlast n z f hf v
  have hq' := physical_substitution hK t' ht0' ht1' htlast' n z g hg v
  have heR := image_removed_added (by omega) n z f g he0 v
  have heA := image_removed_added (by omega) n z g f he1 v
  rw [←heR,heA] at hq'
  apply reciprocal_count _ _ _ _ _ _ hq hq'
  · rintro ⟨x,hx,hr⟩
    exact ⟨x,hx,removed_is_mark hK t ht0 ht1 n z x hr⟩
  · rintro ⟨x,hx,ha⟩ ⟨y,hy,hp⟩
    have he : y=x := hf (hy.trans hx.symm)
    exact added_not_mark hK t ht0 htlast n z x ha (he ▸ hp)
  · intro ha
    obtain ⟨x,hx,hr⟩ := heA.mpr ha
    exact ⟨x,hx,removed_is_mark hK t' ht0' ht1' n z x hr⟩
  · intro hr
    obtain ⟨x,hx,ha⟩ := heR.mp hr
    rintro ⟨y,hy,hp⟩
    have he : y=x := hg (hy.trans hx.symm)
    exact added_not_mark hK t' ht0' htlast' n z x ha (he ▸ hp)

#print axioms reciprocal_preservation
#print axioms agreement_after
#print axioms mark_substitution
#print axioms unchanged
end ErdePaths.AACMarkExchange
