import ErdePaths.BaselinePhysical
import ErdePaths.DenseSourceMarks

namespace ErdePaths.SourcePhysicalMarks
open SourceClock SourceProfile SquareLift OrientedClock HierarchicalDecode

/-- The full baseline geometric union consists of the actual counted source
classes, with actual source factors and a real prescribed endpoint occurrence.
Length and endpoint-phase equalities are explicit transport obligations. -/
theorem anti_source_classes {V : Type} {e K B L b : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hK : 0<K) (hL : 0<L) (hd : 2*L∣K) (hb : b<L) (heven : L%2=0) (hodd : b%2=1)
    (hlen : lengthPower ((2^(e*2^a))*(2^(e*2^a))) h=K*2^r)
    (hperiod : 2^r*L=2^(a+h+1)) (epsilon : Bool) (address : Address (a+h))
    (endpoint : Fin (lengthPower ((2^(e*2^a))*(2^(e*2^a))) h))
    (hcode : endpoint.val%(2^(a+h+1))=(DenseSourceMarks.code r hr epsilon address).val)
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) (j : Fin B) :
    let raw := castClock hlen (SourceProfile.clock he C a h S ho epsilon address)
    let G := OrientedClock.clock (Nat.mul_pos hK (Nat.two_pow_pos r)) raw
      (OrientedClock.index (Nat.mul_pos hK (Nat.two_pow_pos r)) (Fin.cast hlen endpoint)
        (!epsilon) (BaselinePhysical.threshold hK z)) epsilon
    AACMarkIntervals.IsMark hK
      (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) w.1) z (G.position v,j) ↔
      ∃u : Fin b, DenseSourceMarks.Marked he C a h r hr S ho (fun eps _=>!eps)
        epsilon address u.val v := by
  dsimp only
  let raw := castClock hlen (SourceProfile.clock he C a h S ho epsilon address)
  let c := Fin.cast hperiod.symm (DenseSourceMarks.code r hr epsilon address)
  have hc : (Fin.cast hlen endpoint).val%(2^r*L)=c.val := by
    simpa only [Fin.val_cast,c,hperiod] using hcode
  have hh := BaselinePhysical.anti_physical_classes hK (Nat.two_pow_pos r) hL hd hb heven hodd
    raw (Fin.cast hlen endpoint) c hc z epsilon v j
  rw [hh]
  constructor <;> rintro ⟨u,hu⟩ <;> refine ⟨u,?_⟩
  · simpa only [DenseSourceMarks.Marked,shiftedValue,raw,castClock_position,c,Fin.val_cast,hperiod] using hu
  · simpa only [DenseSourceMarks.Marked,shiftedValue,raw,castClock_position,c,Fin.val_cast,hperiod] using hu

#print axioms anti_source_classes
end ErdePaths.SourcePhysicalMarks
