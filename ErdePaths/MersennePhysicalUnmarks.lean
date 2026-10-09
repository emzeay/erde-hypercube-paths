import ErdePaths.BaselinePhysical
import ErdePaths.MersenneOffsets

namespace ErdePaths.MersennePhysicalUnmarks
open SourceClock SquareLift OrientedClock

/-- The four literal lookup positions exhaust the actual long-word bad
predicate. No bad-class membership premise is supplied. -/
theorem bad_iff (P u : Nat) : BaselineResidues.Bad P u ↔
    ∃j : Fin 4, u=MersenneOffsets.bad P j := by
  constructor
  · intro hu
    rcases hu with h|h|h|h
    · exact ⟨⟨0,by decide⟩,h⟩
    · exact ⟨⟨1,by decide⟩,h⟩
    · exact ⟨⟨2,by decide⟩,h⟩
    · exact ⟨⟨3,by decide⟩,h⟩
  · rintro ⟨j,hj⟩
    subst u
    unfold BaselineResidues.Bad MersenneOffsets.bad
    split <;> (try split) <;> (try split) <;> simp_all

theorem bad_bound {P : Nat} (hP : 8≤P) (j : Fin 4) :
    0<MersenneOffsets.bad P j ∧ MersenneOffsets.bad P j<2*P := by
  unfold MersenneOffsets.bad
  split <;> (try split) <;> (try split) <;> omega

/-- Forward is positive; reverse is negative. The real cyclic modulus 4P
and literal four offsets agree, including the seam after the last bad site. -/
theorem signed_delta {P : Nat} (hP : 8≤P) (epsilon : Bool) (j : Fin 4) :
    SourceStability.signedOffset (4*P) 2 (MersenneOffsets.bad P j) (!epsilon)=
      MersenneOffsets.delta P epsilon j := by
  have hb := bad_bound hP j
  have hlt : 2*MersenneOffsets.bad P j<4*P := by omega
  have hsub : 4*P-2*MersenneOffsets.bad P j<4*P := by omega
  cases epsilon <;>
    simp only [SourceStability.signedOffset,MersenneOffsets.delta,
      Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,
      shiftedResidue,Nat.zero_add,Nat.mod_eq_of_lt hlt,Nat.mod_eq_of_lt hsub]

/-- An actual reoriented physical threshold point is unmarked precisely in
one of the four literal delta classes. The genuine full-D endpoint phase is
explicit; no canonical physical representative is substituted. -/
theorem physical_unmarks {U : Type} {K B P : Nat}
    (hK : 0<K) (hP : 8≤P) (hd : 2*P∣K)
    (C : ClockData U (K*2)) (endpoint : Fin (K*2)) (code : Fin (4*P))
    (hcode : endpoint.val%(4*P)=code.val) (z : Fin 2) (epsilon : Bool)
    (v : U) (row : Fin B) :
    let G := clock (Nat.mul_pos hK (by decide)) C
      (index (Nat.mul_pos hK (by decide)) endpoint (!epsilon) (BaselinePhysical.threshold hK z)) epsilon
    ((∃i : Fin K, G.position v=AnchoredEmbedding.positionEncode i z) ∧
      ¬AACMarkIntervals.IsMark hK
        (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1) z (G.position v,row)) ↔
      ∃j : Fin 4, shiftedResidue (4*P) (MersenneOffsets.delta P epsilon j)
        (C.position v).val=code.val := by
  have hmul : 2*(2*P)=4*P := by omega
  have hc : endpoint.val%(2*(2*P))=(Fin.cast hmul.symm code).val := by
    simpa only [hmul,Fin.val_cast] using hcode
  have hh := BaselinePhysical.long_physical_unmarks hK (by decide) hP hd C endpoint
    (Fin.cast hmul.symm code) hc z epsilon v row
  dsimp only at hh ⊢
  rw [hh]
  constructor
  · rintro ⟨u,hu,hx⟩
    obtain ⟨j,hj⟩ := (bad_iff P u.val).mp hu
    refine ⟨j,?_⟩
    rw [hj] at hx
    simpa only [Fin.val_cast,hmul,signed_delta hP] using hx
  · rintro ⟨j,hj⟩
    let u : Fin (2*P) := ⟨MersenneOffsets.bad P j,(bad_bound hP j).2⟩
    refine ⟨u,(bad_iff P u.val).mpr ⟨j,rfl⟩,?_⟩
    change shiftedResidue (2*(2*P))
      (SourceStability.signedOffset (2*(2*P)) 2 (MersenneOffsets.bad P j) (!epsilon))
      (C.position v).val=(Fin.cast hmul.symm code).val
    simpa only [hmul,signed_delta hP,Fin.val_cast] using hj

#print axioms bad_iff
#print axioms signed_delta
#print axioms physical_unmarks
end ErdePaths.MersennePhysicalUnmarks
