import ErdePaths.MersenneSource
import ErdePaths.SourceStability

namespace ErdePaths.MersenneDecode
open SourceClock SourceProfile MersenneSource HierarchicalDecode Profile

/-- Even shifts preserve the actual scalar17 correction, including all cyclic
borrows. No physical-parity identification is assumed. -/
theorem shifted_scalar {M : Nat} (hm : 0<M) (hd : 32∣M) (delta x y : Nat)
    (heven : delta%2=0) (hy : y%32=(17*x)%32) :
    shiftedResidue M delta y%32=(17*shiftedResidue M delta x)%32 := by
  let z := delta%M
  have hz : z<M := Nat.mod_lt _ hm
  have hm32 := Nat.mod_eq_zero_of_dvd hd
  have hz2 : z%2=0 := by
    rw [Nat.mod_mod_of_dvd _ (Nat.dvd_trans (by decide : 2∣32) hd)]
    exact heven
  have hright : (17*shiftedResidue M delta x)%32=(17*(x+(M-z)))%32 := by
    change (17*((x+(M-z))%M))%32=(17*(x+(M-z)))%32
    calc
      _=(17%32*(((x+(M-z))%M)%32))%32 := Nat.mul_mod _ _ _
      _=(17%32*((x+(M-z))%32))%32 := by rw [Nat.mod_mod_of_dvd _ hd]
      _=_ := (Nat.mul_mod _ _ _).symm
  rw [hright]
  simp only [shiftedResidue,Nat.mod_mod_of_dvd _ hd]
  change (y+(M-z))%32=(17*(x+(M-z)))%32
  omega

theorem bit_congr {n x y : Nat} (hm : x%(2^(n+1))=y%(2^(n+1))) : x.testBit n=y.testBit n := by
  have hb := congrArg (fun z => z.testBit n) hm
  simpa only [Nat.testBit_mod_two_pow,show decide (n<n+1)=true from by simp,Bool.true_and] using hb

noncomputable def value {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (address : Address (t+2+h)) : Nat :=
  shiftedResidue (2^(t+2+h+3)) delta ((clock (by omega) C (t+2) h S ho epsilon address).position v).val

noncomputable def corrected {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (address : Address (t+2+h)) : Bool :=
  (value C t h S ho epsilon v delta address).testBit 4 ^^
    (address ⟨1,by omega⟩ && (value C t h S ho epsilon v delta address).testBit 0)

theorem value_low_four {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (a b : Address (t+2+h)) (hp : AgreeBelow 1 a b) :
    value C t h S ho epsilon v delta a%16=value C t h S ho epsilon v delta b%16 := by
  exact SourceStability.shifted_congr (Nat.two_pow_pos _) (by
    change 2^4∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)) delta delta _ _ rfl
    (actual_low_four C (t+2) h (by omega) S S ho ho epsilon epsilon a b hp v)

theorem corrected_false_true {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (heven : delta%2=0) (a b : Address (t+2+h))
    (hp : AgreeBelow 1 a b) (ha : a ⟨1,by omega⟩=false) (hb : b ⟨1,by omega⟩=true) :
    corrected C t h S ho epsilon v delta a=corrected C t h S ho epsilon v delta b := by
  have hscalar := actual_scalar C t h S S ho ho epsilon epsilon a b
    (hp ⟨0,by omega⟩ (by change 0<1; omega)) ha hb v
  have hshift : value C t h S ho epsilon v delta b%32=
      (17*value C t h S ho epsilon v delta a)%32 :=
    shifted_scalar (Nat.two_pow_pos _) (by
      change 2^5∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)) delta _ _ heven hscalar
  have h4 := bit_congr (n:=4) hshift
  rw [scalar_bit] at h4
  have h0 := congrArg (fun n => n%2) (value_low_four C t h S ho epsilon v delta a b hp)
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣16)] at h0
  have hb0 := bit_congr (n:=0) h0
  simp only [corrected,ha,hb,Bool.false_and,Bool.true_and,Bool.xor_false,h4,←hb0]
  simp only [Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

/-- The corrected bit-one decoder is strictly prefix causal even at the small
parent: the actual branch correction is cancelled using actual clock parity. -/
theorem corrected_common {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (heven : delta%2=0) (a b : Address (t+2+h)) (hp : AgreeBelow 1 a b) :
    corrected C t h S ho epsilon v delta a=corrected C t h S ho epsilon v delta b := by
  by_cases heq : a ⟨1,by omega⟩=b ⟨1,by omega⟩
  · have hp2 : AgreeBelow 2 a b := by
      intro i hi
      by_cases hz : i.val=0
      · exact hp i (by omega)
      · have hi1 : i=⟨1,by omega⟩ := Fin.ext (by change i.val=1; omega)
        simpa only [hi1] using heq
    have hclock := lower_prefix_common (by omega) C (t+2) h 2 (by omega)
      (by decide : 32∣lengthPower (2^2) 2) S S ho ho epsilon epsilon a b hp2 v
    have hvalue : value C t h S ho epsilon v delta a%32=value C t h S ho epsilon v delta b%32 :=
      SourceStability.shifted_congr (Nat.two_pow_pos _) (by
        change 2^5∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)) delta delta _ _ rfl hclock
    have h4 := bit_congr (n:=4) hvalue
    have h0 := congrArg (fun n=>n%2) hvalue
    simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣32)] at h0
    have hb0 := bit_congr (n:=0) h0
    simp only [corrected,heq,h4,hb0]
  · cases ha : a ⟨1,by omega⟩ <;> cases hb : b ⟨1,by omega⟩
    · exact False.elim (heq (ha.trans hb.symm))
    · exact corrected_false_true C t h S ho epsilon v delta heven a b hp ha hb
    · exact (corrected_false_true C t h S ho epsilon v delta heven b a
        (fun i hi => (hp i hi).symm) hb ha).symm
    · exact False.elim (heq (ha.trans hb.symm))

noncomputable def bits {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) : Address (t+2+h)→Address (t+2+h) := fun address i =>
  if i.val=0 then (value C t h S ho epsilon v delta address).testBit 0
  else if i.val=1 then corrected C t h S ho epsilon v delta address
  else (value C t h S ho epsilon v delta address).testBit (i.val+3)

/-- The complete exceptional source decoder is derived from actual clocks.
It does not posit the disputed second-bit causality as a premise. -/
theorem bits_causal {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (heven : delta%2=0) : StrictlyCausal (bits C t h S ho epsilon v delta) := by
  intro i a b hp
  by_cases hz : i.val=0
  · simp only [bits,hz,↓reduceIte]
    have hclock := lower_prefix_common (by omega) C (t+2) h 0 (by omega)
      (by decide : 2∣lengthPower (2^2) 0) S S ho ho epsilon epsilon a b (fun _ hi => by omega) v
    apply bit_congr (n:=0)
    exact SourceStability.shifted_congr (Nat.two_pow_pos _) (by
      change 2^1∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)) delta delta _ _ rfl hclock
  · by_cases hi1 : i.val=1
    · simp only [bits,hi1,↓reduceIte]
      exact corrected_common C t h S ho epsilon v delta heven a b (by simpa only [hi1] using hp)
    · simp only [bits,hz,hi1,↓reduceIte]
      have hclock := higher_common (by omega) C (t+2) h (by omega) S ho epsilon i (by omega) a b hp v
      apply bit_congr
      exact SourceStability.shifted_congr (Nat.two_pow_pos _) (by
        apply Nat.pow_dvd_pow; have := i.isLt; omega) delta delta _ _ rfl hclock

/-- Each even physical shift has exactly one exceptional source address, for
arbitrary source depth, selector family and fixed profile twin. -/
theorem unique_source {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (heven : delta%2=0) :
    ∃a, a=bits C t h S ho epsilon v delta a ∧
      ∀b, b=bits C t h S ho epsilon v delta b → b=a := by
  let F := bits C t h S ho epsilon v delta
  have hc := bits_causal C t h S ho epsilon v delta heven
  let target : Address (t+2+h) := fun _ => false
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

theorem boolean_slot : ∀b0 b1 c : Bool, b1=(c ^^ (b1 && b0)) ↔ c=(b1 && !b0) := by decide

/-- The decoded second source uses the literal non-injective paper code
b1·(1−b0), with uniqueness supplied by the corrected actual inverse clock. -/
theorem owner_slots {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (a : Address (t+2+h)) (hf : a=bits C t h S ho epsilon v delta a) :
    a ⟨0,by omega⟩=(value C t h S ho epsilon v delta a).testBit 0 ∧
    (value C t h S ho epsilon v delta a).testBit 4=(a ⟨1,by omega⟩ && !a ⟨0,by omega⟩) ∧
    (∀i : Fin (t+2+h), 2≤i.val → a i=(value C t h S ho epsilon v delta a).testBit (i.val+3)) := by
  have h0 := congrFun hf ⟨0,by omega⟩
  simp only [bits,↓reduceIte] at h0
  have h1 := congrFun hf ⟨1,by omega⟩
  simp only [bits,show (1=0)=False from propext (by decide),↓reduceIte,corrected] at h1
  rw [←h0] at h1
  refine ⟨h0,(boolean_slot _ _ _).mp h1,?_⟩
  intro i hi
  have hh := congrFun hf i
  simpa only [bits,ite_eq_right (show i.val≠0 by omega),ite_eq_right (show i.val≠1 by omega)] using hh

noncomputable def Slots {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (a : Address (t+2+h)) : Prop :=
    a ⟨0,by omega⟩=(value C t h S ho epsilon v delta a).testBit 0 ∧
    (value C t h S ho epsilon v delta a).testBit 4=(a ⟨1,by omega⟩ && !a ⟨0,by omega⟩) ∧
    (∀i : Fin (t+2+h), 2≤i.val → a i=(value C t h S ho epsilon v delta a).testBit (i.val+3))

theorem fixed_iff_slots {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (a : Address (t+2+h)) :
    a=bits C t h S ho epsilon v delta a ↔ Slots C t h S ho epsilon v delta a := by
  constructor
  · exact owner_slots C t h S ho epsilon v delta a
  · rintro ⟨h0,h4,hh⟩
    funext i
    by_cases hz : i.val=0
    · have hi : i=⟨0,by omega⟩ := Fin.ext hz
      rw [hi]
      simpa only [bits,↓reduceIte] using h0
    · by_cases ho1 : i.val=1
      · have hi : i=⟨1,by omega⟩ := Fin.ext ho1
        rw [hi]
        simp only [bits,↓reduceIte,corrected]
        rw [←h0]
        exact (boolean_slot _ _ _).mpr h4
      · simpa only [bits,ite_eq_right hz,ite_eq_right ho1] using hh i (by omega)

/-- Unique inversion of the actual non-injective slot code. The separate
profile/hole constraints and physical unmark incidence are not asserted. -/
theorem unique_slots {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (delta : Nat) (heven : delta%2=0) :
    ∃a, Slots C t h S ho epsilon v delta a ∧
      ∀b, Slots C t h S ho epsilon v delta b → b=a := by
  obtain ⟨a,ha,hu⟩ := unique_source C t h S ho epsilon v delta heven
  exact ⟨a,(fixed_iff_slots C t h S ho epsilon v delta a).mp ha,
    fun b hb => hu b ((fixed_iff_slots C t h S ho epsilon v delta b).mpr hb)⟩

#print axioms unique_slots
#print axioms bits_causal
#print axioms unique_source
#print axioms owner_slots
#print axioms corrected_common
end ErdePaths.MersenneDecode
