import ErdePaths.SourceProfile

namespace ErdePaths.SourceLengths
open SourceClock SourceProfile

/-- Literal length of the lower/profile/upper hierarchy. -/
theorem source_length (e a h : Nat) :
    lengthPower ((2^(e*2^a))*(2^(e*2^a))) h=2^(e*2^(a+h+1)) := by
  rw [←Nat.pow_add,lengthPower_pow]
  congr 1
  rw [←Nat.mul_two,Nat.pow_succ,Nat.pow_add]
  ac_rfl

private theorem exponential_room (T : Nat) : T+1≤2^T := by
  induction T with
  | zero => decide
  | succ T ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos T; omega

theorem source_exponent_room {e : Nat} (he : 2≤e) (a h : Nat) :
    a+h+2≤e*2^(a+h+1) := by
  have ht := exponential_room (a+h+1)
  have hm := Nat.mul_le_mul_right (2^(a+h+1)) he
  omega

/-- The fine clock is K*A with canonical power-of-two coarse size. -/
theorem fine_length {e : Nat} (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) :
    lengthPower ((2^(e*2^a))*(2^(e*2^a))) h=
      2^(e*2^(a+h+1)-r)*2^r := by
  rw [source_length,←Nat.pow_add]
  congr 1
  have hh := source_exponent_room he a h
  omega

/-- The source code period is A*L with no truncated exponent. -/
theorem code_period (a h r : Nat) (hr : r<a+h+1) :
    2^r*2^(a+h+1-r)=2^(a+h+1) := by
  rw [←Nat.pow_add]
  congr 1
  omega

/-- The complete balanced anti-period divides the actual coarse size. -/
theorem coarse_period {e : Nat} (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) :
    2*2^(a+h+1-r)∣2^(e*2^(a+h+1)-r) := by
  have hh := source_exponent_room he a h
  have ht : a+h+1-r+1≤e*2^(a+h+1)-r := by omega
  have hd := Nat.pow_dvd_pow 2 ht
  simpa only [Nat.pow_succ,Nat.mul_comm] using hd

theorem coarse_size {e : Nat} (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) :
    4≤2^(e*2^(a+h+1)-r) := by
  have hh := source_exponent_room he a h
  have ht : 2≤e*2^(a+h+1)-r := by omega
  exact Nat.pow_le_pow_right (show 1≤2 by decide) ht

theorem block_even (a h r : Nat) (hr : r<a+h+1) : 2^(a+h+1-r)%2=0 := by
  have ht : a+h+1-r=(a+h+1-r-1)+1 := by omega
  rw [ht,Nat.pow_succ]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

#print axioms fine_length
#print axioms coarse_period
end ErdePaths.SourceLengths
