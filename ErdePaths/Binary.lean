import ErdePaths.Basic

namespace ErdePaths

/-- The literal binary tuple represented by a bounded integer. -/
def binaryTuple {n : Nat} (u : Vertex n) : Fin n → Bool :=
  fun i => u.val.testBit i.val

theorem binaryTuple_injective {n : Nat} : Function.Injective (@binaryTuple n) := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · have hn : n ≤ i := by omega
    have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hn
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le u.isLt hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.isLt hp)]

private def binaryValue : {n : Nat} → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => 2 * binaryValue (fun i : Fin n => f i.succ) + (f 0).toNat

private theorem binaryValue_lt {n : Nat} (f : Fin n → Bool) : binaryValue f < 2 ^ n := by
  induction n with
  | zero => simp [binaryValue]
  | succ n ih =>
    have h := ih (fun i => f i.succ)
    have hb : (f 0).toNat < 2 := by cases f 0 <;> decide
    simp only [binaryValue, Nat.pow_succ]
    omega

private theorem binaryValue_bits {n : Nat} (f : Fin n → Bool) (i : Fin n) :
    (binaryValue f).testBit i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hb : (f 0).toNat < 2 ^ 1 := by cases f 0 <;> decide
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [binaryValue, ← Nat.pow_one 2]
      rw [Nat.testBit_two_pow_mul_add _ hb]
      simp
      cases f 0 <;> rfl
    · rw [binaryValue, ← Nat.pow_one 2]
      rw [Nat.testBit_two_pow_mul_add _ hb]
      simpa using ih (fun k => f k.succ) j

theorem binaryTuple_surjective {n : Nat} : Function.Surjective (@binaryTuple n) := by
  intro f
  refine ⟨⟨binaryValue f, binaryValue_lt f⟩, ?_⟩
  funext i
  exact binaryValue_bits f i

/-- The adjacency definition is literally exactly-one-coordinate difference
under the now kernel-verified bijection with binary tuples. -/
theorem adjacent_iff_tuple {n : Nat} (u v : Vertex n) :
    Adjacent u v ↔ ∃ d : Fin n, binaryTuple u d ≠ binaryTuple v d ∧
      ∀ i : Fin n, i ≠ d → binaryTuple u i = binaryTuple v i := Iff.rfl

#print axioms binaryTuple_injective
#print axioms binaryTuple_surjective
end ErdePaths
