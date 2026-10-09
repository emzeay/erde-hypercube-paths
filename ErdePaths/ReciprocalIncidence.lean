import ErdePaths.AACMarkExchange

namespace ErdePaths.ReciprocalIncidence
open AACMarkExchange AACMarkIntervals AACInduction
attribute [local instance] Classical.propDecidable

/-- Exact incidence arithmetic for reciprocal deletions/additions. -/
theorem count_exchange (P P' R A Q Q' : Prop)
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

/-- Physical exchange preservation needs equality of endpoint IMAGE SETS.
Different H clocks may enumerate the same physical rows in different orders. -/
theorem preservation {K A B : Nat} {U : Type} (hK : 1<K)
    (t t' : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (SquareLift.predecessor (by omega) ⟨0,by omega⟩)=true)
    (ht0' : t' ⟨0,by omega⟩=false) (ht1' : t' ⟨1,hK⟩=false)
    (htlast' : t' (SquareLift.predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (f g : (Fin (K*A) × Fin B)→U)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (heR : ∀v, ImageSet f (Removed (by omega) n z) v↔ImageSet g (Added (by omega) n z) v)
    (heA : ∀v, ImageSet g (Removed (by omega) n z) v↔ImageSet f (Added (by omega) n z) v)
    (v : U) :
    incidence (ImageSet f (IsMark (by omega) (turnsAfter (by omega) t n) z) v)+
      incidence (ImageSet g (IsMark (by omega) (turnsAfter (by omega) t' n) z) v)=
    incidence (ImageSet f (IsMark (by omega) (fun w=>t w.1) z) v)+
      incidence (ImageSet g (IsMark (by omega) (fun w=>t' w.1) z) v) := by
  have hq := physical_substitution hK t ht0 ht1 htlast n z f hf v
  have hq' := physical_substitution hK t' ht0' ht1' htlast' n z g hg v
  rw [←heR v,heA v] at hq'
  apply count_exchange _ _ _ _ _ _ hq hq'
  · rintro ⟨x,hx,hr⟩
    exact ⟨x,hx,removed_is_mark hK t ht0 ht1 n z x hr⟩
  · rintro ⟨x,hx,ha⟩ ⟨y,hy,hp⟩
    have he : y=x := hf (hy.trans hx.symm)
    exact added_not_mark hK t ht0 htlast n z x ha (he ▸ hp)
  · intro ha
    obtain ⟨x,hx,hr⟩ := (heA v).mpr ha
    exact ⟨x,hx,removed_is_mark hK t' ht0' ht1' n z x hr⟩
  · intro hr
    obtain ⟨x,hx,ha⟩ := (heR v).mp hr
    rintro ⟨y,hy,hp⟩
    have he : y=x := hg (hy.trans hx.symm)
    exact added_not_mark hK t' ht0' htlast' n z x ha (he ▸ hp)

#print axioms preservation
end ErdePaths.ReciprocalIncidence
