import ErdePaths.AACPatternCardinality
import ErdePaths.AACFoldClock

namespace ErdePaths.UniformFoldLengths

/-- Exact ordinary fold arithmetic, with arbitrary positive dimensions and
arbitrary odd remainder. The required room prevents truncated exponents. -/
theorem ordinary {g H j r s b : Nat} (room : r+s≤g) (hj : 1≤j) :
    2^(j-1)*(2^(g-r)*2^H*(2^r+1)+b*(2^(g-r)/2^s)*2^H)=
      (2^(r+s)+2^s+b)*2^(g+H+j-(r+s)-1) := by
  have hk : 2^(g-r)=2^(g-(r+s))*2^s := by
    rw [←Nat.pow_add]; congr 1; omega
  have hd : 2^(g-r)/2^s=2^(g-(r+s)) := by
    rw [hk,Nat.mul_div_cancel]; exact Nat.two_pow_pos s
  rw [hd,hk]
  have hp : 2^s*2^r=2^(r+s) := by rw [←Nat.pow_add,Nat.add_comm]
  have hs : 2^(g-(r+s))*2^s*2^H*(2^r+1)+b*2^(g-(r+s))*2^H=
      (2^(r+s)+2^s+b)*(2^(g-(r+s))*2^H) := by
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.add_mul]
    have he : 2^(g-(r+s))*2^s*2^H*2^r=2^(r+s)*(2^(g-(r+s))*2^H) := by
      rw [←hp]; ac_rfl
    rw [he]; ac_rfl
  rw [hs]
  have he : 2^(j-1)*(2^(g-(r+s))*2^H)=2^(g+H+j-(r+s)-1) := by
    rw [←Nat.pow_add,←Nat.pow_add]; congr 1; omega
  rw [←Nat.mul_assoc,Nat.mul_comm (2^(j-1)),Nat.mul_assoc,he]

/-- Long-word fold arithmetic. This treats every Mersenne depth uniformly;
no individual odd-part certificate enters the statement. -/
theorem mersenne {g H j R : Nat} (room : R+2≤g) (hR : 1≤R) (hj : 1≤j) :
    2^(j-1)*(2^(g-1)*2^H*3+(2*2^R-4)*(2^(g-1)/(2*2^R))*2^H)=
      (2^(R+1)-1)*2^(g+H+j-R-1) := by
  have hk : 2^(g-1)=2^(g-R-2)*(2*2^R) := by
    rw [Nat.mul_comm 2,←Nat.pow_succ,←Nat.pow_add]; congr 1; omega
  have hp : 0<2*2^R := Nat.mul_pos (by decide) (Nat.two_pow_pos R)
  have hd : 2^(g-1)/(2*2^R)=2^(g-R-2) := by
    rw [hk,Nat.mul_div_cancel]; exact hp
  have hP : 2≤2^R := Nat.pow_le_pow_right (by decide : 1≤2) hR
  have ha : 3*(2*2^R)+(2*2^R-4)=4*(2^(R+1)-1) := by
    rw [Nat.pow_succ]; omega
  rw [hd,hk]
  have hs : 2^(g-R-2)*(2*2^R)*2^H*3+(2*2^R-4)*2^(g-R-2)*2^H=
      (2^(R+1)-1)*(4*(2^(g-R-2)*2^H)) := by
    calc
      _=(3*(2*2^R)+(2*2^R-4))*(2^(g-R-2)*2^H) := by rw [Nat.add_mul]; ac_rfl
      _=_ := by rw [ha]; ac_rfl
  rw [hs]
  have he : 2^(j-1)*(4*(2^(g-R-2)*2^H))=2^(g+H+j-R-1) := by
    change 2^(j-1)*(2^2*(2^(g-R-2)*2^H))=_
    rw [←Nat.pow_add,←Nat.pow_add,←Nat.pow_add]; congr 1; omega
  rw [←Nat.mul_assoc,Nat.mul_comm (2^(j-1)),Nat.mul_assoc,he]

#print axioms ordinary
#print axioms mersenne
end ErdePaths.UniformFoldLengths
