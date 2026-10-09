import ErdePaths.Parameters

namespace ErdePaths.SourceRoom

/-- A uniform prefix choice avoids searching over special odd parts. -/
theorem non_mersenne_bound (t : Nat) : t+3≤2*2^(t+1) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t+1+1=(t+1)+1 by omega,Nat.pow_succ,←Nat.mul_assoc,Nat.mul_two]
    omega

theorem mersenne_bound (t : Nat) : t+6≤2*2^(t+2) := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [show t+1+2=(t+2)+1 by omega,Nat.pow_succ,←Nat.mul_assoc,Nat.mul_two]
    omega

theorem prefix_room {m r : Nat} (hm : 1≤m) (hr : 3≤r) :
    r≤2*m*2^(r-2) := by
  have hh := non_mersenne_bound (r-3)
  have he : r-3+3=r := by omega
  have he' : r-3+1=r-2 := by omega
  rw [he,he'] at hh
  have hp := Nat.mul_le_mul_right (2^(r-2)) (show 2≤2*m by omega)
  omega

theorem mersenne_prefix_room {m r : Nat} (hm : 1≤m) (hr : 4≤r) :
    r+2≤2*m*2^(r-2) := by
  have hh := mersenne_bound (r-4)
  have he : r-4+6=r+2 := by omega
  have he' : r-4+2=r-2 := by omega
  rw [he,he'] at hh
  have hp := Nat.mul_le_mul_right (2^(r-2)) (show 2≤2*m by omega)
  omega

/-- k=r−2 prefix squares, one profile, and one upper square give exactly
r factor-choice bits; the full address modulus divides the actual prefix length. -/
theorem fixed_prefix {m r : Nat} (hm : 1≤m) (hr : 3≤r) :
    (r-2)+1+1=r ∧ 1≤r-(r-2)-1 ∧
      2^r∣2^(2*m*2^(r-2)) := by
  exact ⟨by omega,by omega,Nat.pow_dvd_pow 2 (prefix_room hm hr)⟩

/-- The same choice supplies the stronger modulus used by complementary
Mersenne unmarks, without restricting dimension or binary complexity. -/
theorem fixed_mersenne_prefix {m r : Nat} (hm : 1≤m) (hr : 4≤r) :
    2≤r-2 ∧ (r-2)+1+1=r ∧
      2^(r+2)∣2^(2*m*2^(r-2)) := by
  exact ⟨by omega,by omega,Nat.pow_dvd_pow 2 (mersenne_prefix_room hm hr)⟩

#print axioms fixed_prefix
#print axioms fixed_mersenne_prefix
end ErdePaths.SourceRoom
