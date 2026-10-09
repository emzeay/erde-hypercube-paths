import ErdePaths.MersenneUnmarks

namespace ErdePaths.MersenneCode
open SourceClock SourceProfile MersenneDecode MersenneUnmarks HierarchicalDecode

/-- The exceptional full numeric code, including both zero holes. -/
def codeBits {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K) : Fin (K+3)→Bool := fun i =>
  if i.val=0 then a ⟨0,by omega⟩
  else if i.val=1 then epsilon
  else if i.val=2 ∨ i.val=3 then false
  else if i.val=4 then if exceptional then a ⟨1,by omega⟩ && !a ⟨0,by omega⟩ else a ⟨1,by omega⟩
  else a ⟨i.val-3,by have := i.isLt; omega⟩

noncomputable def code {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K) : Vertex (K+3) :=
  Classical.choose (binaryTuple_surjective (codeBits hk exceptional epsilon a))

theorem code_bits {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K) :
    binaryTuple (code hk exceptional epsilon a)=codeBits hk exceptional epsilon a :=
  Classical.choose_spec (binaryTuple_surjective (codeBits hk exceptional epsilon a))

theorem low_digits_finite : ∀x : Fin 16, ∀epsilon : Bool,
    x.val=x.val%2+2*epsilon.toNat ↔
      x.val.testBit 1=epsilon ∧ x.val.testBit 2=false ∧ x.val.testBit 3=false := by
  decide

theorem low_digits (x : Nat) (epsilon : Bool) :
    x%16=x%2+2*epsilon.toNat ↔
      x.testBit 1=epsilon ∧ x.testBit 2=false ∧ x.testBit 3=false := by
  have hh := low_digits_finite ⟨x%16,Nat.mod_lt _ (by decide)⟩ epsilon
  simpa only [Nat.mod_mod_of_dvd _ (by decide : 2∣16),show 16=2^4 from rfl,
    Nat.testBit_mod_two_pow,show decide (1<4)=true from rfl,
    show decide (2<4)=true from rfl,show decide (3<4)=true from rfl,Bool.true_and] using hh

def Slots {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K) (x : Nat) : Prop :=
  a ⟨0,by omega⟩=x.testBit 0 ∧
  x.testBit 4=(if exceptional then a ⟨1,by omega⟩ && !a ⟨0,by omega⟩ else a ⟨1,by omega⟩) ∧
  (∀i : Fin K, 2≤i.val → a i=x.testBit (i.val+3)) ∧
  x%16=x%2+2*epsilon.toNat

/-- No address injectivity is asserted: repeated codes in the odd branch
are faithfully retained. Equality nevertheless checks every numeric bit. -/
theorem eq_code_iff {K : Nat} (hk : 2≤K) (exceptional epsilon : Bool) (a : Address K)
    (x : Vertex (K+3)) : x=code hk exceptional epsilon a ↔ Slots hk exceptional epsilon a x.val := by
  constructor
  · intro he
    have hb := code_bits hk exceptional epsilon a
    rw [←he] at hb
    have hb0 := congrFun hb ⟨0,by omega⟩
    have hb1 := congrFun hb ⟨1,by omega⟩
    have hb2 := congrFun hb ⟨2,by omega⟩
    have hb3 := congrFun hb ⟨3,by omega⟩
    have hb4 := congrFun hb ⟨4,by omega⟩
    simp only [binaryTuple,codeBits,↓reduceIte] at hb0 hb1 hb2 hb3 hb4
    refine ⟨hb0.symm,hb4,?_,(low_digits x.val epsilon).mpr ⟨hb1,hb2,hb3⟩⟩
    intro i hi
    have hh := congrFun hb ⟨i.val+3,by have := i.isLt; omega⟩
    have hn0 : i.val+3≠0 := by omega
    have hn1 : i.val+3≠1 := by omega
    have hn23 : ¬(i.val+3=2 ∨ i.val+3=3) := by omega
    have hn4 : i.val+3≠4 := by omega
    simp only [binaryTuple,codeBits,ite_eq_right hn0,ite_eq_right hn1,
      ite_eq_right hn23,ite_eq_right hn4,Nat.add_sub_cancel] at hh
    exact hh.symm
  · rintro ⟨h0,h4,hh,hlow⟩
    obtain ⟨h1,h2,h3⟩ := (low_digits x.val epsilon).mp hlow
    apply binaryTuple_injective
    rw [code_bits]
    funext i
    unfold binaryTuple codeBits
    by_cases hz : i.val=0
    · simpa only [hz,↓reduceIte] using h0.symm
    · simp only [ite_eq_right hz]
      by_cases ho : i.val=1
      · simpa only [ho,↓reduceIte] using h1
      · simp only [ite_eq_right ho]
        by_cases h23 : i.val=2 ∨ i.val=3
        · simp only [ite_eq_left h23]
          rcases h23 with h | h
          · simpa only [h] using h2
          · simpa only [h] using h3
        · simp only [ite_eq_right h23]
          by_cases hf : i.val=4
          · simpa only [hf,↓reduceIte] using h4
          · simp only [ite_eq_right hf]
            have hi : 2≤i.val-3 := by omega
            have hb := hh ⟨i.val-3,by have := i.isLt; omega⟩ hi
            simpa only [show i.val-3+3=i.val by omega] using hb.symm

/-- The actual unmark definition is exactly literal cyclic full-code
membership, including reserved profile and hole slots. -/
theorem unmarked_iff_code {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (epsilon : Bool) (j : Fin 4) (a : AddressType t h) :
    Unmarked C t h S ho v epsilon j a ↔
      value C t h S ho epsilon v (MersenneOffsets.delta (phase t h) epsilon j) a=
        (code (by omega) true epsilon a).val := by
  let x : Vertex (t+2+h+3) := ⟨value C t h S ho epsilon v
    (MersenneOffsets.delta (phase t h) epsilon j) a,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have hc := eq_code_iff (by omega : 2≤t+2+h) true epsilon a x
  rw [Fin.ext_iff] at hc
  change _ ↔ x.val=(code (by omega) true epsilon a).val
  rw [hc]
  unfold Unmarked MersenneDecode.Slots Slots
  simp only [x,and_assoc,↓reduceIte]


/-- Complete literal numeric class ownership; no profile or hole constraint
is left implicit in this statement. -/
theorem unique_code_owner {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (hroom : 1≤t+h)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    ∃epsilon j a,
      value C t h S ho epsilon v (MersenneOffsets.delta (phase t h) epsilon j) a=
        (code (by omega) true epsilon a).val ∧
      ∀epsilon' j' a',
        value C t h S ho epsilon' v (MersenneOffsets.delta (phase t h) epsilon' j') a'=
          (code (by omega) true epsilon' a').val →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨epsilon,j,a,hm,hu⟩ := unique_unmark C t h hroom S ho v
  refine ⟨epsilon,j,a,(unmarked_iff_code C t h S ho v epsilon j a).mp hm,?_⟩
  intro epsilon' j' a' hc
  exact hu epsilon' j' a' ((unmarked_iff_code C t h S ho v epsilon' j' a').mpr hc)

#print axioms unique_code_owner

#print axioms unmarked_iff_code
#print axioms eq_code_iff
end ErdePaths.MersenneCode
