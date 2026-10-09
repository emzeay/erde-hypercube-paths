import ErdePaths.MersenneLargeDecode
import ErdePaths.MersenneOffsets

namespace ErdePaths.MersenneLargeUnmarks
open MersenneUnmarks (shifted_parity zero_shift_mod)
open SourceClock SourceProfile MersenneSource MersenneLargeDecode HierarchicalDecode Profile MersenneOffsets

abbrev AddressType (k h : Nat) := Address (k+h)

/-- Full phase modulus is 4P; the source code's reserved holes are 2,3. -/
def phase (k h : Nat) : Nat := 2^(k+h+1)

theorem modulus (k h : Nat) : 2^(k+h+3)=4*phase k h := by
  unfold phase
  rw [show k+h+3=(k+h+1)+2 by omega,Nat.pow_add]
  omega

theorem phase_four {k h : Nat} (hroom : 3≤k+h) : 16≤phase k h := by
  change 2^4≤2^(k+h+1)
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem phase_div {k h : Nat} (hroom : 3≤k+h) : 16∣phase k h := by
  change 2^4∣2^(k+h+1)
  exact Nat.pow_dvd_pow 2 (by omega)

/-- The first source bit is common for actual owners, despite different
profile twins, offsets, and all later source branches. -/
theorem first_common {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (d : Nat) (he : d%2=0) (a rho : AddressType k h)
    (ha : Slots hebase C k h hk S ho epsilon v d a)
    (hr : Slots hebase C k h hk S ho false v 0 rho) : a ⟨0,by omega⟩=rho ⟨0,by omega⟩ := by
  have hc := lower_prefix_common (by omega) C (k) h 0 (by omega)
    (by change 2^1∣2^e; exact Nat.pow_dvd_pow 2 (by omega)) S S ho ho epsilon false a rho
    (fun _ hi => by omega) v
  have hd : 2∣2^(k+h+3) := by
    change 2^1∣2^(k+h+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpa := shifted_parity (Nat.two_pow_pos _) hd
    ((clock (by omega) C (k) h S ho epsilon a).position v).val d he
  have hpr := shifted_parity (Nat.two_pow_pos _) hd
    ((clock (by omega) C (k) h S ho false rho).position v).val 0 rfl
  have hv : value hebase C k h S ho epsilon v d a%2=value hebase C k h S ho false v 0 rho%2 :=
    hpa.trans (hc.trans hpr.symm)
  exact ha.1.trans ((MersenneDecode.bit_congr (n:=0) hv).trans hr.1.symm)

def Unmarked {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (epsilon : Bool) (j : Fin 4) (address : AddressType k h) : Prop :=
  Slots hebase C k h hk S ho epsilon v (delta (phase k h) epsilon j) address ∧
  value hebase C k h S ho epsilon v (delta (phase k h) epsilon j) address%16=
    (value hebase C k h S ho epsilon v (delta (phase k h) epsilon j) address)%2+2*epsilon.toNat

/-- Raw actual low clock values are shared by all candidate owners. -/
theorem owner_low_common {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (d : Nat) (he : d%2=0) (a rho : AddressType k h)
    (ha : Slots hebase C k h hk S ho epsilon v d a)
    (hr : Slots hebase C k h hk S ho false v 0 rho) :
    value hebase C k h S ho epsilon v 0 a%16=value hebase C k h S ho false v 0 rho%16 := by
  apply value_low_four_cross
where
  value_low_four_cross : value hebase C k h S ho epsilon v 0 a%16=value hebase C k h S ho false v 0 rho%16 := by
    have hp : AgreeBelow 1 a rho := by
      intro i hi
      have hi0 : i=⟨0,by omega⟩ := Fin.ext (by change i.val=0; omega)
      rw [hi0]
      exact first_common hebase C k h hk S ho epsilon v d he a rho ha hr
    have hd : 16∣lengthPower (2^e) 1 := by
      rw [lengthPower_pow]
      change 2^4∣2^(e*2^1)
      exact Nat.pow_dvd_pow 2 (by omega)
    have hc := lower_prefix_common (by omega) C k h 1 (by omega) hd S S ho ho epsilon false a rho hp v
    exact SourceStability.shifted_congr (Nat.two_pow_pos _) (by
      change 2^4∣2^(k+h+3); exact Nat.pow_dvd_pow 2 (by omega)) 0 0 _ _ rfl hc


/-- Changing shift keeps the actual raw clock; low congruence at shift zero
therefore transports with every borrow retained. -/
theorem shift_low {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (d x : Nat) (a : AddressType k h)
    (hc : value hebase C k h S ho epsilon v 0 a%16=x%16) :
    value hebase C k h S ho epsilon v d a%16=shiftedResidue (2^(k+h+3)) d x%16 := by
  have hd : 16∣2^(k+h+3) := by
    change 2^4∣2^(k+h+3); exact Nat.pow_dvd_pow 2 (by omega)
  apply SourceStability.shifted_congr (Nat.two_pow_pos _) hd d d _ _ rfl
  exact (zero_shift_mod hd _).symm.trans hc

theorem unmarked_iff_tag {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (hroom : 3≤k+h)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (epsilon : Bool) (j : Fin 4) (a rho : AddressType k h)
    (ha : Slots hebase C k h hk S ho epsilon v (delta (phase k h) epsilon j) a)
    (hr : Slots hebase C k h hk S ho false v 0 rho) :
    Unmarked hebase C k h hk S ho v epsilon j a ↔
      (tag epsilon j).val=(value hebase C k h S ho false v 0 rho)%16/2 := by
  let x := value hebase C k h S ho false v 0 rho
  let d := delta (phase k h) epsilon j
  have hp := phase_four hroom
  have hd := phase_div hroom
  have he : d%2=0 := delta_even hp epsilon j
  have hc := owner_low_common hebase C k h hk S ho epsilon v d he a rho ha hr
  have hs := shift_low hebase C k h hk S ho epsilon v d x a hc
  rw [modulus] at hs
  have hpar : value hebase C k h S ho epsilon v d a%2=x%2 := by
    have hh := congrArg (fun z=>z%2) hs
    simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣16)] at hh
    exact hh.trans (shifted_parity (by omega) (by omega) x d he)
  change (Slots hebase C k h hk S ho epsilon v d a ∧
    value hebase C k h S ho epsilon v d a%16=value hebase C k h S ho epsilon v d a%2+2*epsilon.toNat) ↔ _
  rw [and_iff_right ha,hs,hpar]
  exact low_iff_tag hp hd x epsilon j

/-- Exactly one actual source/profile factor and one disagreement offset
unmarks every physical vertex, uniformly in the full source depth. -/
theorem unique_unmark {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (hroom : 3≤k+h)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h) :
    ∃epsilon j a, Unmarked hebase C k h hk S ho v epsilon j a ∧
      ∀epsilon' j' a', Unmarked hebase C k h hk S ho v epsilon' j' a' →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨rho,hr,_⟩ := unique_slots hebase C k h hk S ho false v 0
  let x := value hebase C k h S ho false v 0 rho
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  have he := delta_even (phase_four hroom) c.1 c.2
  obtain ⟨a,ha,hu⟩ := unique_slots hebase C k h hk S ho c.1 v (delta (phase k h) c.1 c.2)
  have hm := (unmarked_iff_tag hebase C k h hk hroom S ho v c.1 c.2 a rho ha hr).mpr
    (congrArg Fin.val hc)
  refine ⟨c.1,c.2,a,hm,?_⟩
  intro epsilon' j' a' hm'
  have ht := (unmarked_iff_tag hebase C k h hk hroom S ho v epsilon' j' a' rho hm'.1 hr).mp hm'
  have htag : tag epsilon' j'=tag c.1 c.2 := by
    apply Fin.ext
    exact ht.trans (congrArg Fin.val hc).symm
  have hpair := tag_bijection.2 (epsilon',j') c htag
  have heps := congrArg Prod.fst hpair
  have hj := congrArg Prod.snd hpair
  change epsilon'=c.1 at heps
  change j'=c.2 at hj
  refine ⟨heps,hj,?_⟩
  apply hu
  simpa only [heps,hj] using hm'.1

/-- Larger-base raw slots plus low16 constraints are exactly literal full
numeric unmark membership: epsilon and both holes are checked explicitly. -/
theorem unmarked_iff_code {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (epsilon : Bool) (j : Fin 4) (a : AddressType k h) :
    Unmarked hebase C k h hk S ho v epsilon j a ↔
      value hebase C k h S ho epsilon v (delta (phase k h) epsilon j) a=
        (MersenneCode.code (by omega) false epsilon a).val :=
  (MersenneLargeDecode.full_code_iff hebase C k h hk S ho epsilon v
    (delta (phase k h) epsilon j) a).symm

/-- Complete actual numeric code ownership for all larger bases and arbitrary
source depth: there is no presumed profile/hole owner among the premises. -/
theorem unique_code_owner {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (hroom : 3≤k+h)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃epsilon j a,
      value hebase C k h S ho epsilon v (delta (phase k h) epsilon j) a=
        (MersenneCode.code (by omega) false epsilon a).val ∧
      ∀epsilon' j' a',
        value hebase C k h S ho epsilon' v (delta (phase k h) epsilon' j') a'=
          (MersenneCode.code (by omega) false epsilon' a').val →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨epsilon,j,a,hm,hu⟩ := unique_unmark hebase C k h hk hroom S ho v
  refine ⟨epsilon,j,a,(unmarked_iff_code hebase C k h hk S ho v epsilon j a).mp hm,?_⟩
  intro epsilon' j' a' hc
  exact hu epsilon' j' a' ((unmarked_iff_code hebase C k h hk S ho v epsilon' j' a').mpr hc)

#print axioms unique_code_owner
#print axioms unique_unmark
#print axioms unmarked_iff_tag
#print axioms owner_low_common
end ErdePaths.MersenneLargeUnmarks
