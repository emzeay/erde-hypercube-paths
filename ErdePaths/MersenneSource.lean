import ErdePaths.SourceProfile
import ErdePaths.MersenneClock

namespace ErdePaths.MersenneSource
open SourceClock SourceProfile HierarchicalDecode Profile MersenneClock

/-- The higher sparse positions have room uniformly, beginning at source bit 2. -/
theorem high_exponent {e j : Nat} (he : 2≤e) (hj : 2≤j) : j+4≤e*2^j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : 2≤j
    · have hh := ih h
      rw [Nat.pow_succ,←Nat.mul_assoc,Nat.mul_two]
      omega
    · have htwo : j=1 := by omega
      subst j
      omega

/-- The exceptional second source branch is derived at its literal N=16
parent, then propagated through every later prefix square. -/
theorem prefix_scalar {V : Type} (C : ClockData V (2^2)) (t : Nat)
    (address address' : Address (t+2))
    (hzero : address ⟨0,by omega⟩=address' ⟨0,by omega⟩)
    (hfalse : address ⟨1,by omega⟩=false)
    (htrue : address' ⟨1,by omega⟩=true)
    (v : VertexPower V (t+2)) :
    ((iteratedClock (Nat.two_pow_pos 2) C (t+2) address').position v).val%32=
      (17*((iteratedClock (Nat.two_pow_pos 2) C (t+2) address).position v).val)%32 := by
  induction t with
  | zero =>
    change ((squareClock (by decide) (squareClock (by decide) C (address' ⟨0,by omega⟩))
      (address' ⟨1,by omega⟩)).position v).val%32=
      (17*((squareClock (by decide) (squareClock (by decide) C (address ⟨0,by omega⟩))
        (address ⟨1,by omega⟩)).position v).val)%32
    rw [hfalse,htrue,←hzero]
    exact scalar_clock _ v
  | succ t ih =>
    change ((squareClock _ (iteratedClock _ C (t+2) (fun i => address' i.castSucc))
      (address' (Fin.last (t+2)))).position v).val%32=_
    apply square_scalar _ _ _ _ _ _
    · rw [lengthPower_pow]
      change 2^5∣_
      exact Nat.pow_dvd_pow 2 (by have := high_exponent (e:=2) (j:=t+2) (by omega) (by omega); omega)
    · intro u
      exact ih (fun i => address i.castSucc) (fun i => address' i.castSucc)
        hzero hfalse htrue u

/-- Scalar17 applies to the actual fresh profile and all upper squares,
including unrelated selector functions and profile twins. -/
theorem actual_scalar {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S T : Address (t+2) → Fin (2^(2*2^(t+2))) → Bool)
    (hs : ∀ x, cardinality (S x)%2=1) (ht : ∀ x, cardinality (T x)%2=1)
    (epsilon epsilon' : Bool) (address address' : Address (t+2+h))
    (hzero : address ⟨0,by omega⟩=address' ⟨0,by omega⟩)
    (hfalse : address ⟨1,by omega⟩=false)
    (htrue : address' ⟨1,by omega⟩=true)
    (v : VertexPower (VertexPower V (t+2) × VertexPower V (t+2)) h) :
    ((clock (by omega) C (t+2) h T ht epsilon' address').position v).val%32=
      (17*((clock (by omega) C (t+2) h S hs epsilon address).position v).val)%32 := by
  have hd : 32∣2^(2*2^(t+2)) := by
    change 2^5∣_
    exact Nat.pow_dvd_pow 2 (by
    have := high_exponent (e:=2) (j:=t+2) (by omega) (by omega); omega)
  apply descendants_scalar _ (Nat.dvd_trans hd (Nat.dvd_mul_right _ _))
  intro u
  apply profile_scalar _ hd
  intro w
  simp only [prefixClock,castClock_position]
  exact prefix_scalar C t (lowerAddress address) (lowerAddress address') hzero hfalse htrue w

/-- At larger bases, the second source branch has no modulo32 correction;
all selectors, twins and suffix addresses are invisible at this modulus. -/
theorem actual_second_common {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 1≤k)
    (S T : Address k → Fin (2^(e*2^k)) → Bool)
    (hs : ∀ x, cardinality (S x)%2=1) (ht : ∀ x, cardinality (T x)%2=1)
    (epsilon epsilon' : Bool) (address address' : Address (k+h))
    (hp : AgreeBelow 1 address address')
    (v : VertexPower (VertexPower V k × VertexPower V k) h) :
    ((clock (by omega) C k h S hs epsilon address).position v).val%32=
      ((clock (by omega) C k h T ht epsilon' address').position v).val%32 := by
  apply lower_prefix_common (by omega) C k h 1 hk _ S T hs ht epsilon epsilon' address address' hp v
  rw [lengthPower_pow]
  change 2^5∣_
  apply Nat.pow_dvd_pow 2
  omega

/-- Source j>=2 occupies slot j+3: its entire clock residue through that slot
is strictly prefix causal in the actual hierarchy. -/
theorem higher_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ x, cardinality (S x)%2=1) (epsilon : Bool)
    (i : Fin (k+h)) (hi : 2≤i.val) (address address' : Address (k+h))
    (hp : AgreeBelow i.val address address')
    (v : VertexPower (VertexPower V k × VertexPower V k) h) :
    ((clock he C k h S ho epsilon address).position v).val%(2^(i.val+4))=
      ((clock he C k h S ho epsilon address').position v).val%(2^(i.val+4)) := by
  by_cases hik : i.val≤k
  · apply lower_prefix_common he C k h i.val hik _ S S ho ho epsilon epsilon address address' hp v
    rw [lengthPower_pow]
    exact Nat.pow_dvd_pow 2 (high_exponent he hi)
  · have hd0 : 2^(k+4)∣(2^(e*2^k))*(2^(e*2^k)) := by
      rw [←Nat.pow_add]
      exact Nat.pow_dvd_pow 2 (by have := high_exponent he hk; omega)
    have hev : 2∣(2^(e*2^k))*(2^(e*2^k)) :=
      Nat.dvd_trans (by simpa using Nat.pow_dvd_pow 2 (show 1≤k+4 by omega)) hd0
    have hd := offset_bit_modulus hd0 hev (i.val-k)
    rw [show k+4+(i.val-k)=i.val+4 by omega] at hd
    exact upper_prefix_common he C k h i.val (by omega) (by have := i.isLt; omega) hd
      S ho epsilon address address' hp v

/-- Scalar17 toggles bit4 exactly on odd input residue. This bounded arithmetic
identity is used only to read the already proved uniform physical clock law. -/
theorem scalar_bit (n : Nat) : (17*n).testBit 4=(n.testBit 4 ^^ n.testBit 0) := by
  have hh : ∀ x : Fin 32, (17*x.val).testBit 4=(x.val.testBit 4 ^^ x.val.testBit 0) := by decide
  have h := hh ⟨n%32,Nat.mod_lt _ (by omega)⟩
  have hleft : (17*(n%32)).testBit 4=(17*n).testBit 4 := by
    have hm : (17*(n%32))%32=(17*n)%32 := by simp [Nat.mul_mod]
    have hb := congrArg (fun z => z.testBit 4) hm
    simpa only [show 32=2^5 from rfl,Nat.testBit_mod_two_pow,
      show decide (4<5)=true from rfl,Bool.true_and] using hb
  have hright : ((n%32).testBit 4 ^^(n%32).testBit 0)=(n.testBit 4 ^^n.testBit 0) := by
    simp only [show 32=2^5 from rfl,Nat.testBit_mod_two_pow,
      show decide (4<5)=true from rfl,show decide (0<5)=true from rfl,Bool.true_and]
  exact hleft.symm.trans (h.trans hright)

/-- The small-base source correction is a statement about actual physical
inverse-clock bits. No unproved identification of bit0 with source bit0 occurs. -/
theorem actual_bit {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S T : Address (t+2) → Fin (2^(2*2^(t+2))) → Bool)
    (hs : ∀ x, cardinality (S x)%2=1) (ht : ∀ x, cardinality (T x)%2=1)
    (epsilon epsilon' : Bool) (address address' : Address (t+2+h))
    (hzero : address ⟨0,by omega⟩=address' ⟨0,by omega⟩)
    (hfalse : address ⟨1,by omega⟩=false)
    (htrue : address' ⟨1,by omega⟩=true)
    (v : VertexPower (VertexPower V (t+2) × VertexPower V (t+2)) h) :
    ((clock (by omega) C (t+2) h T ht epsilon' address').position v).val.testBit 4=
      (((clock (by omega) C (t+2) h S hs epsilon address).position v).val.testBit 4 ^^
       ((clock (by omega) C (t+2) h S hs epsilon address).position v).val.testBit 0) := by
  have hm := actual_scalar C t h S T hs ht epsilon epsilon' address address' hzero hfalse htrue v
  have hb := congrArg (fun z => z.testBit 4) hm
  simp only [show 32=2^5 from rfl,Nat.testBit_mod_two_pow,
    show decide (4<5)=true from rfl,Bool.true_and] at hb
  exact hb.trans (scalar_bit _)

/-- The lower four bits of the exceptional second sibling remain common
across every actual suffix, selector and twin. -/
theorem actual_low_four {V : Type} (C : ClockData V (2^2)) (k h : Nat) (hk : 1≤k)
    (S T : Address k → Fin (2^(2*2^k)) → Bool)
    (hs : ∀ x, cardinality (S x)%2=1) (ht : ∀ x, cardinality (T x)%2=1)
    (epsilon epsilon' : Bool) (address address' : Address (k+h))
    (hp : AgreeBelow 1 address address')
    (v : VertexPower (VertexPower V k × VertexPower V k) h) :
    ((clock (by omega) C k h S hs epsilon address).position v).val%16=
      ((clock (by omega) C k h T ht epsilon' address').position v).val%16 :=
  lower_prefix_common (by omega) C k h 1 hk (by decide) S T hs ht epsilon epsilon' address address' hp v

#print axioms actual_bit
#print axioms actual_scalar
#print axioms actual_second_common
#print axioms higher_common
end ErdePaths.MersenneSource
