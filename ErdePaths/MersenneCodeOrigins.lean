import ErdePaths.SourcePairedArcs
import ErdePaths.MersenneCode
import ErdePaths.DenseCodeTwins

namespace ErdePaths.MersenneCodeOrigins
open SourceClock SourceProfile PairedArc HierarchicalDecode

theorem profile_bit {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K) :
    (MersenneCode.code hk exceptional epsilon a).val.testBit 1=epsilon := by
  have hh := congrFun (MersenneCode.code_bits hk exceptional epsilon a) ⟨1,by omega⟩
  simpa [binaryTuple,MersenneCode.codeBits] using hh

/-- Exceptional codes may repeat across addresses. At each fixed address
changing the reserved profile bit still gives the literal increment two. -/
theorem code_true {K : Nat} (hk : 2≤K) (exceptional : Bool) (a : Address K) :
    (MersenneCode.code hk exceptional true a).val=
      (MersenneCode.code hk exceptional false a).val+2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hn := profile_bit hk exceptional false a
  have hi := DenseCodeTwins.add_unset_bit 1 _ hn i
  change ((MersenneCode.code hk exceptional false a).val+2).testBit i=
    if i=1 then true else (MersenneCode.code hk exceptional false a).val.testBit i at hi
  rw [hi]
  by_cases h1 : i=1
  · subst i; simp only [ite_true,profile_bit]
  · rw [ite_eq_right h1]
    by_cases hb : i<K+3
    · have ht := congrFun (MersenneCode.code_bits hk exceptional true a) ⟨i,hb⟩
      have hf := congrFun (MersenneCode.code_bits hk exceptional false a) ⟨i,hb⟩
      by_cases h0 : i=0
      · simp only [binaryTuple,MersenneCode.codeBits,h0,↓reduceIte] at ht hf
        simpa only [h0] using ht.trans hf.symm
      · simp only [binaryTuple,MersenneCode.codeBits,ite_eq_right h0,ite_eq_right h1] at ht hf
        exact ht.trans hf.symm
    · have hp : 2^(K+3)≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (MersenneCode.code hk exceptional true a).isLt hp),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (MersenneCode.code hk exceptional false a).isLt hp)]

theorem endpoint_phase {K : Nat} (hk : 2≤K) (exceptional : Bool) (a : Address K) :
    ((MersenneCode.code hk exceptional false a).val+2)%2^(K+3)=
      (MersenneCode.code hk exceptional true a).val := by
  rw [←code_true hk exceptional a]
  exact Nat.mod_eq_of_lt (MersenneCode.code hk exceptional true a).isLt

/-- Paired physical endpoints at the full Mersenne modulus. No phase
occurrence or arc-existence hypothesis is supplied. -/
theorem exists_pair {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k+h) (hh : 0<h)
    (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, Profile.cardinality (S a)%2=1) (exceptional : Bool) (a : Address (k+h))
    (hbalance : Profile.prefixCount (S (lowerAddress a)) 2=1) :
    ∃p : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
        (SourceProfile.clock he C k h S ho false a) 2,
    ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
        (SourceProfile.clock he C k h S ho true a) 2,
      p.vertex ⟨0,by omega⟩=q.vertex ⟨0,by omega⟩ ∧
      p.vertex ⟨2,by omega⟩=q.vertex ⟨2,by omega⟩ ∧
      ((SourceProfile.clock he C k h S ho false a).position (p.vertex ⟨0,by omega⟩)).val%2^(k+h+3)=
        (MersenneCode.code hk exceptional false a).val ∧
      ((SourceProfile.clock he C k h S ho true a).position (q.vertex ⟨2,by omega⟩)).val%2^(k+h+3)=
        (MersenneCode.code hk exceptional true a).val := by
  have hshort : 2<2^(k+h+3) := by
    have hp := Nat.pow_le_pow_right (show 1≤2 by decide) (show 2≤k+h+3 by omega)
    omega
  let c := MersenneCode.code hk exceptional false a
  obtain ⟨p,q,hs,he',hp⟩ := SourcePairedArcs.paired (u:=1) he (Nat.two_pow_pos _) C k h hh room
    hshort S ho a hbalance c
  refine ⟨p,q,hs,he',?_,?_⟩
  · simpa only [Nat.add_zero,Nat.mod_eq_of_lt c.isLt,c] using (hp ⟨0,by omega⟩).1
  · exact ((hp ⟨2,by omega⟩).2).trans (endpoint_phase hk exceptional a)

structure Data {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k+h) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, Profile.cardinality (S a)%2=1) (exceptional : Bool) (a : Address (k+h)) where
  arcFalse : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
    (SourceProfile.clock he C k h S ho false a) 2
  arcTrue : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
    (SourceProfile.clock he C k h S ho true a) 2
  start_equal : arcFalse.vertex ⟨0,by omega⟩=arcTrue.vertex ⟨0,by omega⟩
  end_equal : arcFalse.vertex ⟨2,by omega⟩=arcTrue.vertex ⟨2,by omega⟩
  false_code : ((SourceProfile.clock he C k h S ho false a).position
    (arcFalse.vertex ⟨0,by omega⟩)).val%2^(k+h+3)=(MersenneCode.code hk exceptional false a).val
  true_code : ((SourceProfile.clock he C k h S ho true a).position
    (arcTrue.vertex ⟨2,by omega⟩)).val%2^(k+h+3)=(MersenneCode.code hk exceptional true a).val

noncomputable def family {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k+h) (hh : 0<h) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (hbalance : ∀a : Address (k+h), Profile.prefixCount (S (lowerAddress a)) 2=1)
    (exceptional : Bool) (a : Address (k+h)) : Data he C k h hk S ho exceptional a :=
  Classical.choice (by
    obtain ⟨p,q,hs,he',hc,hc'⟩ := exists_pair he C k h hk hh room S ho exceptional a (hbalance a)
    exact ⟨⟨p,q,hs,he',hc,hc'⟩⟩)

noncomputable def endpoint {V : Type} {e k h : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hk : 2≤k+h} {S : Address k→Fin (2^(e*2^k))→Bool}
    {ho : ∀a, Profile.cardinality (S a)%2=1} {exceptional : Bool} {a : Address (k+h)}
    (D : Data he C k h hk S ho exceptional a) (epsilon : Bool) :
    Fin (lengthPower ((2^(e*2^k))*(2^(e*2^k))) h) :=
  if epsilon then (SourceProfile.clock he C k h S ho true a).position (D.arcTrue.vertex ⟨2,by omega⟩)
  else (SourceProfile.clock he C k h S ho false a).position (D.arcFalse.vertex ⟨0,by omega⟩)

theorem endpoint_code {V : Type} {e k h : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hk : 2≤k+h} {S : Address k→Fin (2^(e*2^k))→Bool}
    {ho : ∀a, Profile.cardinality (S a)%2=1} {exceptional : Bool} {a : Address (k+h)}
    (D : Data he C k h hk S ho exceptional a) (epsilon : Bool) :
    (endpoint D epsilon).val%2^(k+h+3)=(MersenneCode.code hk exceptional epsilon a).val := by
  cases epsilon
  · exact D.false_code
  · exact D.true_code

theorem endpoint_vertex {V : Type} {e k h : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hk : 2≤k+h} {S : Address k→Fin (2^(e*2^k))→Bool}
    {ho : ∀a, Profile.cardinality (S a)%2=1} {exceptional : Bool} {a : Address (k+h)}
    (D : Data he C k h hk S ho exceptional a) (epsilon : Bool) :
    (SourceProfile.clock he C k h S ho epsilon a).cycle (endpoint D epsilon)=
      if epsilon then D.arcTrue.vertex ⟨2,by omega⟩ else D.arcFalse.vertex ⟨0,by omega⟩ := by
  cases epsilon <;> simp only [endpoint,Bool.false_eq_true,ite_false,ite_true]
  · exact (SourceProfile.clock he C k h S ho false a).cycle_position _
  · exact (SourceProfile.clock he C k h S ho true a).cycle_position _

#print axioms code_true
#print axioms exists_pair
#print axioms endpoint_code
end ErdePaths.MersenneCodeOrigins
