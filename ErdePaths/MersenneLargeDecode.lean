import ErdePaths.MersenneSource
import ErdePaths.MersenneCode

namespace ErdePaths.MersenneLargeDecode
open SourceClock SourceProfile MersenneSource HierarchicalDecode Profile

/-- Literal larger-base source slots: profile1, holes2/3, source1 at4,
and source j>=2 atj+3. -/
def slot (j : Nat) : Nat := if j=0 then 0 else if j=1 then 4 else j+3

noncomputable def value {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (delta : Nat) (address : Address (k+h)) : Nat :=
  shiftedResidue (2^(k+h+3)) delta ((clock (by omega) C k h S ho epsilon address).position v).val

noncomputable def bits {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (delta : Nat) : Address (k+h)→Address (k+h) := fun address i =>
  (value he C k h S ho epsilon v delta address).testBit (slot i.val)

/-- Strict prefix causality is derived from actual lower/suffix constructors;
no supplied output clock congruence or decoded owner is an input. -/
theorem bits_causal {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) :
    StrictlyCausal (bits he C k h S ho epsilon v delta) := by
  intro i a b hp
  change (value he C k h S ho epsilon v delta a).testBit (slot i.val)=
    (value he C k h S ho epsilon v delta b).testBit (slot i.val)
  apply MersenneDecode.bit_congr
  apply SourceStability.shifted_congr (Nat.two_pow_pos _) _ delta delta _ _ rfl
  · by_cases hz : i.val=0
    · simp only [slot,hz,↓reduceIte]
      apply lower_prefix_common (by omega) C k h 0 (by omega) _ S S ho ho epsilon epsilon a b
        (fun _ hi => by omega) v
      change 2^1∣2^e
      exact Nat.pow_dvd_pow 2 (by omega)
    · by_cases hone : i.val=1
      · simp only [slot,hone,↓reduceIte,Nat.one_ne_zero]
        exact actual_second_common he C k h (by omega) S S ho ho epsilon epsilon a b
          (by simpa only [hone] using hp) v
      · simp only [slot,ite_eq_right hz,ite_eq_right hone]
        exact higher_common (by omega) C k h hk S ho epsilon i (by omega) a b hp v
  · by_cases hz : i.val=0
    · simp only [slot,hz,↓reduceIte]
      change 2^1∣2^(k+h+3)
      exact Nat.pow_dvd_pow 2 (by omega)
    · by_cases hone : i.val=1
      · simp only [slot,hone,↓reduceIte,Nat.one_ne_zero]
        exact Nat.pow_dvd_pow 2 (by omega)
      · simp only [slot,ite_eq_right hz,ite_eq_right hone]
        exact Nat.pow_dvd_pow 2 (by have := i.isLt; omega)

/-- Every arithmetic shift, not only even shifts, has a unique actual source
address at larger bases. Reserved epsilon/zero holes remain separate slots. -/
theorem unique_source {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) :
    ∃a, a=bits he C k h S ho epsilon v delta a ∧
      ∀b, b=bits he C k h S ho epsilon v delta b→b=a := by
  let F := bits he C k h S ho epsilon v delta
  have hc := bits_causal he C k h hk S ho epsilon v delta
  let target : Address (k+h) := fun _ => false
  let a := HierarchicalDecode.decode F target
  have hh := decode_correct F hc target
  have hf : a=F a := by
    funext i
    have hi := congrFun hh i
    change (a i ^^ F a i)=false at hi
    exact Bool.xor_left_inj.mp (hi.trans (Bool.xor_self (F a i)).symm)
  refine ⟨a,hf,?_⟩
  intro b hb
  apply (unique_solution F hc target).2 b
  funext i
  change (b i ^^ F b i)=false
  rw [congrFun hb i,Bool.xor_self]

noncomputable def Slots {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) (a : Address (k+h)) : Prop :=
  a ⟨0,by omega⟩=(value he C k h S ho epsilon v delta a).testBit 0 ∧
  a ⟨1,by omega⟩=(value he C k h S ho epsilon v delta a).testBit 4 ∧
  (∀ i : Fin (k+h), 2≤i.val→a i=(value he C k h S ho epsilon v delta a).testBit (i.val+3))

theorem fixed_iff_slots {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) (a : Address (k+h)) :
    a=bits he C k h S ho epsilon v delta a ↔ Slots he C k h hk S ho epsilon v delta a := by
  constructor
  · intro ha
    refine ⟨?_,?_,?_⟩
    · simpa only [bits,slot,↓reduceIte,Nat.one_ne_zero,ite_false] using congrFun ha ⟨0,by omega⟩
    · simpa only [bits,slot,↓reduceIte,Nat.one_ne_zero,ite_false] using congrFun ha ⟨1,by omega⟩
    · intro i hi
      simpa only [bits,slot,ite_eq_right (show i.val≠0 by omega),ite_eq_right (show i.val≠1 by omega)]
        using congrFun ha i
  · rintro ⟨h0,h1,hh⟩
    funext i
    by_cases hz : i.val=0
    · have hi : i=⟨0,by omega⟩ := Fin.ext hz
      rw [hi]
      simpa only [bits,slot,↓reduceIte,Nat.one_ne_zero,ite_false] using h0
    · by_cases hone : i.val=1
      · have hi : i=⟨1,by omega⟩ := Fin.ext hone
        rw [hi]
        simpa only [bits,slot,↓reduceIte,Nat.one_ne_zero,ite_false] using h1
      · simpa only [bits,slot,ite_eq_right hz,ite_eq_right hone] using hh i (by omega)

theorem unique_slots {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) :
    ∃a, Slots he C k h hk S ho epsilon v delta a ∧
      ∀b, Slots he C k h hk S ho epsilon v delta b→b=a := by
  obtain ⟨a,ha,hu⟩ := unique_source he C k h hk S ho epsilon v delta
  exact ⟨a,(fixed_iff_slots he C k h hk S ho epsilon v delta a).mp ha,
    fun b hb => hu b ((fixed_iff_slots he C k h hk S ho epsilon v delta b).mpr hb)⟩

/-- Complete large-base literal code membership, including reserved bit1 and
both zero holes, is exactly raw source Slots plus the explicit low16 equation. -/
theorem full_code_iff {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (delta : Nat) (a : Address (k+h)) :
    value he C k h S ho epsilon v delta a=(MersenneCode.code (by omega) false epsilon a).val ↔
      Slots he C k h hk S ho epsilon v delta a ∧
      value he C k h S ho epsilon v delta a%16=
        value he C k h S ho epsilon v delta a%2+2*epsilon.toNat := by
  let x : Vertex (k+h+3) := ⟨value he C k h S ho epsilon v delta a,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have hc := MersenneCode.eq_code_iff (by omega : 2≤k+h) false epsilon a x
  rw [Fin.ext_iff] at hc
  change x.val=(MersenneCode.code (by omega) false epsilon a).val ↔ _
  rw [hc]
  unfold MersenneCode.Slots Slots
  simp only [x]
  constructor
  · rintro ⟨h0,h1,hh,hl⟩
    exact ⟨⟨h0,h1.symm,hh⟩,hl⟩
  · rintro ⟨⟨h0,h1,hh⟩,hl⟩
    exact ⟨h0,h1.symm,hh,hl⟩

#print axioms full_code_iff
#print axioms bits_causal
#print axioms unique_slots
end ErdePaths.MersenneLargeDecode
