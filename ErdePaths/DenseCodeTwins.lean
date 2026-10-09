import ErdePaths.DenseSourceMarks

namespace ErdePaths.DenseCodeTwins
open DenseSourceMarks HierarchicalDecode

/-- Adding a power of two to an unset bit changes only that bit: there is
no carry into any higher slot. -/
theorem add_unset_bit (r n : Nat) (hn : n.testBit r=false) (i : Nat) :
    (n+2^r).testBit i=if i=r then true else n.testBit i := by
  induction r generalizing n i with
  | zero =>
    have hm : n%2=0 := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hn
    cases i with
    | zero =>
      have hmod : (n+1)%2=1 := by omega
      simp only [Nat.pow_zero,ite_true,Nat.testBit_zero,hmod,decide_true]
    | succ i =>
      simp only [Nat.pow_zero,Nat.testBit_succ,show i+1≠0 by omega,ite_false]
      have hd : (n+1)/2=n/2 := by omega
      rw [hd]
  | succ r ih =>
    have hn' : (n/2).testBit r=false := by simpa only [Nat.testBit_succ] using hn
    cases i with
    | zero =>
      rw [Nat.add_comm n, Nat.testBit_two_pow_add_gt (show 0<r+1 by omega)]
      simp only [show 0≠r+1 by omega,ite_false]
    | succ i =>
      rw [Nat.testBit_succ,Nat.testBit_succ]
      have hd : (n+2^(r+1))/2=n/2+2^r := by
        rw [Nat.pow_succ,Nat.add_mul_div_right n (2^r) (by decide)]
      rw [hd,ih (n/2) hn' i]
      simp only [Nat.succ.injEq]

/-- The literal false/true representative codes differ by exactly the
reserved power of two, for every address and reserved slot. -/
theorem code_true {K : Nat} (r : Nat) (hr : r<K+1) (address : Address K) :
    (code r hr true address).val=(code r hr false address).val+2^r := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [add_unset_bit r _ (code_reserved r hr false address) i]
  by_cases hir : i=r
  · subst i
    simp only [ite_true,code_reserved]
  · rw [ite_eq_right hir]
    by_cases hi : i<K+1
    · have ht := congrFun (code_bits r hr true address) ⟨i,hi⟩
      have hf := congrFun (code_bits r hr false address) ⟨i,hi⟩
      simp only [ErdePaths.binaryTuple,codeBits,dite_eq_right hir] at ht hf
      exact ht.trans hf.symm
    · have hp : 2^(K+1)≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (code r hr true address).isLt hp),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (code r hr false address).isLt hp)]

/-- The twin increment stays inside the complete code range; endpoint
phase agreement therefore does not conceal a wrap or extra carry. -/
theorem code_false_add_lt {K : Nat} (r : Nat) (hr : r<K+1) (address : Address K) :
    (code r hr false address).val+2^r<2^(K+1) := by
  rw [←code_true r hr address]
  exact (code r hr true address).isLt

/-- Prescribing the false code at the initial vertex of a 2^r-edge arc
prescribes the literal true code at its endpoint. -/
theorem code_endpoint_phase {K : Nat} (r : Nat) (hr : r<K+1) (address : Address K) :
    ((code r hr false address).val+2^r)%2^(K+1)=(code r hr true address).val := by
  rw [Nat.mod_eq_of_lt (code_false_add_lt r hr address)]
  exact (code_true r hr address).symm

#print axioms add_unset_bit
#print axioms code_true
#print axioms code_false_add_lt
#print axioms code_endpoint_phase
end ErdePaths.DenseCodeTwins
