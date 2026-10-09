import ErdePaths.OrientedClock
import ErdePaths.PairedArc
import ErdePaths.SourceStability

namespace ErdePaths.AACResidueBridge
open SourceClock SquareLift SourceStability OrientedClock

def reduce {N P : Nat} (hP : 0<P) (t : Fin N) : Fin P :=
  ⟨t.val%P,Nat.mod_lt _ hP⟩

theorem reduce_forward {N P : Nat} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (a t : Fin N) : reduce hP (forward hN a t)=forward hP (reduce hP a) (reduce hP t) := by
  apply Fin.ext
  simp only [reduce,forward,Nat.mod_mod_of_dvd _ hd]
  exact Nat.add_mod _ _ _

theorem reduce_backward {N P : Nat} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (a t : Fin N) : reduce hP (backward hN a t)=backward hP (reduce hP a) (reduce hP t) := by
  apply Fin.ext
  change ((N-t.val+a.val)%N)%P=(P-t.val%P+a.val%P)%P
  rw [Nat.mod_mod_of_dvd _ hd]
  exact PairedArc.difference_phase hP hd t.isLt

theorem reduce_index {N P : Nat} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (a t : Fin N) (epsilon : Bool) :
    reduce hP (index hN a epsilon t)=index hP (reduce hP a) epsilon (reduce hP t) := by
  cases epsilon
  · exact reduce_backward hN hP hd a t
  · exact reduce_forward hN hP hd a t

private theorem add_comm {P} (hP : 0<P) (a b : Fin P) : forward hP a b=forward hP b a := by
  apply Fin.ext
  exact congrArg (fun n=>n%P) (Nat.add_comm _ _)

private theorem add_assoc {P} (hP : 0<P) (a b c : Fin P) :
    forward hP (forward hP a b) c=forward hP a (forward hP b c) := by
  apply Fin.ext
  simp only [forward,Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]

/-- The fine-grid offset z cancels the actual rotated/reversed origin. -/
theorem offset_cancel {P} (hP : 0<P) (c z d : Fin P) (epsilon : Bool) :
    index hP (index hP c (!epsilon) z) epsilon (forward hP d z)=index hP c epsilon d := by
  cases epsilon
  · change backward hP (forward hP c z) (forward hP d z)=backward hP c d
    apply forward_injective hP (forward hP d z)
    rw [forward_inverse]
    symm
    calc
      forward hP (forward hP d z) (backward hP c d) =
          forward hP (backward hP c d) (forward hP d z) := add_comm hP _ _
      _ = forward hP (forward hP (backward hP c d) d) z := (add_assoc hP _ _ _).symm
      _ = forward hP (forward hP d (backward hP c d)) z := by rw [add_comm hP (backward hP c d) d]
      _ = forward hP c z := by rw [forward_inverse]
  · change forward hP (backward hP c z) (forward hP d z)=forward hP c d
    rw [add_comm hP d z,←add_assoc,add_comm hP (backward hP c z) z,forward_inverse]

/-- A literal physical coordinate at d+z has raw source phase c+d for the
forward twin and c-d for the reverse twin. This is uniform in every modulus. -/
theorem physical_phase {V N P} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (C : ClockData V N) (c z t : Fin N) (d : Fin P) (epsilon : Bool)
    (ht : reduce hP t=forward hP d (reduce hP z)) :
    reduce hP (C.position ((clock hN C (index hN c (!epsilon) z) epsilon).cycle t))=
      index hP (reduce hP c) epsilon d := by
  simp only [clock,C.position_cycle]
  rw [reduce_index hN hP hd,reduce_index hN hP hd,ht]
  exact offset_cancel hP _ _ _ epsilon

private theorem forward_negative {P} (hP : 0<P) (c d : Fin P) :
    forward hP (backward hP ⟨0,hP⟩ d) c=backward hP c d := by
  apply forward_injective hP d
  rw [forward_inverse,←add_assoc,forward_inverse,add_comm hP ⟨0,hP⟩ c,forward_zero]

/-- The shift API uses a negative flag, hence !epsilon. Literal residue
membership is exactly the raw phase of the oriented coordinate. -/
theorem shifted_signed_iff {P} (hP : 0<P) (c x d : Fin P) (epsilon : Bool) :
    shiftedResidue P (signedOffset P 1 d.val (!epsilon)) x.val=c.val ↔
      x=index hP c epsilon d := by
  let delta : Fin P := ⟨signedOffset P 1 d.val (!epsilon),by
    cases epsilon <;> simp only [signedOffset,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,↓reduceIte,Nat.one_mul]
    · exact Nat.mod_lt _ hP
    · exact Nat.mod_lt _ hP⟩
  have hb : shiftedResidue P delta.val x.val=(backward hP x delta).val := by
    simp only [shiftedResidue,backward,Nat.mod_eq_of_lt delta.isLt]
    rw [Nat.add_comm]
  have he : backward hP x delta=c ↔ x=forward hP delta c := by
    constructor
    · intro hh
      rw [←hh,forward_inverse]
    · intro hh
      rw [hh,HamiltonNormalize.unrotate_rotate]
  have hi : forward hP delta c=index hP c epsilon d := by
    cases epsilon
    · have hh : delta=backward hP ⟨0,hP⟩ d := by
        apply Fin.ext
        simp only [delta,signedOffset,Bool.not_false,↓reduceIte,Nat.one_mul,
          shiftedResidue,backward,Nat.zero_add,Nat.add_zero,Nat.mod_eq_of_lt d.isLt]
      rw [hh,forward_negative]
      rfl
    · have hh : delta=d := by
        apply Fin.ext
        simp only [delta,signedOffset,Bool.not_true,Bool.false_eq_true,↓reduceIte,
          Nat.one_mul,Nat.mod_eq_of_lt d.isLt]
      rw [hh,add_comm]
      rfl
  change shiftedResidue P delta.val x.val=c.val ↔ _
  rw [hb,←Fin.ext_iff,he,hi]

/-- At each actual fine coordinate d+z, its physical vertex belongs to
exactly the corresponding signed source residue class. -/
theorem physical_residue {V N P} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (C : ClockData V N) (c z t : Fin N) (d : Fin P) (epsilon : Bool)
    (ht : reduce hP t=forward hP d (reduce hP z)) :
    shiftedResidue P (signedOffset P 1 d.val (!epsilon))
      (C.position ((clock hN C (index hN c (!epsilon) z) epsilon).cycle t)).val=
        (reduce hP c).val := by
  have hp := physical_phase hN hP hd C c z t d epsilon ht
  have hh := (shifted_signed_iff hP (reduce hP c)
    (reduce hP (C.position ((clock hN C (index hN c (!epsilon) z) epsilon).cycle t)))
    d epsilon).mpr hp
  simpa only [reduce,shiftedResidue,Nat.mod_add_mod] using hh

theorem index_injective {P} (hP : 0<P) (c : Fin P) (epsilon : Bool) :
    Function.Injective (index hP c epsilon) := by
  intro x y he
  have hh := congrArg (inverse hP c epsilon) he
  simpa only [inverse_index] using hh

/-- Full physical incidence, not merely membership for selected coordinates.
Every vertex of the genuine clock is tested by its actual oriented position. -/
theorem physical_residue_iff {V N P} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (C : ClockData V N) (c z : Fin N) (d : Fin P) (epsilon : Bool) (v : V) :
    shiftedResidue P (signedOffset P 1 d.val (!epsilon)) (C.position v).val=
        (reduce hP c).val ↔
      reduce hP ((clock hN C (index hN c (!epsilon) z) epsilon).position v)=
        forward hP d (reduce hP z) := by
  let D := clock hN C (index hN c (!epsilon) z) epsilon
  have hx : reduce hP (C.position v)=
      index hP (index hP (reduce hP c) (!epsilon) (reduce hP z)) epsilon
        (reduce hP (D.position v)) := by
    have hh := congrArg (fun w=>reduce hP (C.position w)) (D.cycle_position v)
    simp only [D,clock,C.position_cycle] at hh
    rw [reduce_index hN hP hd,reduce_index hN hP hd] at hh
    exact hh.symm
  have hs : shiftedResidue P (signedOffset P 1 d.val (!epsilon)) (C.position v).val=
        (reduce hP c).val ↔
      reduce hP (C.position v)=index hP (reduce hP c) epsilon d := by
    have hh := shifted_signed_iff hP (reduce hP c) (reduce hP (C.position v)) d epsilon
    simpa only [reduce,shiftedResidue,Nat.mod_add_mod] using hh
  rw [hs,hx,←offset_cancel hP (reduce hP c) (reduce hP z) d epsilon]
  exact (index_injective hP _ epsilon).eq_iff

/-- The same physical incidence with an unreduced spacing A*u. -/
theorem physical_spaced_residue_iff {V N P} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (C : ClockData V N) (c z : Fin N) (A u : Nat) (epsilon : Bool) (v : V) :
    shiftedResidue P (signedOffset P A u (!epsilon)) (C.position v).val=
        c.val%P ↔
      ((clock hN C (index hN c (!epsilon) z) epsilon).position v).val%P=
        (A*u+z.val)%P := by
  let d : Fin P := ⟨(A*u)%P,Nat.mod_lt _ hP⟩
  have hs : signedOffset P 1 d.val (!epsilon)=signedOffset P A u (!epsilon) := by
    cases epsilon <;> simp only [signedOffset,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,↓reduceIte,Nat.one_mul,d,shiftedResidue,Nat.mod_mod]
  have hh := physical_residue_iff hN hP hd C c z d epsilon v
  rw [hs] at hh
  simpa only [reduce,d,forward,Fin.ext_iff,Nat.mod_add_mod,Nat.add_mod_mod] using hh

/-- Canonical actual parent-clock occurrence of any phase code. -/
def codeOccurrence {N P} (hN : 0<N) (hd : P∣N) (c : Fin P) : Fin N :=
  ⟨c.val,Nat.lt_of_lt_of_le c.isLt (Nat.le_of_dvd hN hd)⟩

/-- Every literal residue class is the corresponding oriented coordinate
class when the origin is constructed from its code; no phase existence input. -/
theorem canonical_incidence {V N P} (hN : 0<N) (hP : 0<P) (hd : P∣N)
    (C : ClockData V N) (c : Fin P) (z : Fin N) (A u : Nat) (epsilon : Bool) (v : V) :
    shiftedResidue P (signedOffset P A u (!epsilon)) (C.position v).val=c.val ↔
      ((clock hN C (index hN (codeOccurrence hN hd c) (!epsilon) z) epsilon).position v).val%P=
        (A*u+z.val)%P := by
  have hh := physical_spaced_residue_iff hN hP hd C (codeOccurrence hN hd c) z A u epsilon v
  simpa only [codeOccurrence,Nat.mod_eq_of_lt c.isLt] using hh

#print axioms canonical_incidence
#print axioms physical_residue_iff
#print axioms physical_residue
#print axioms physical_phase
end ErdePaths.AACResidueBridge
