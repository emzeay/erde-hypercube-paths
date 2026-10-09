import ErdePaths.MersenneOffsets

namespace ErdePaths.MersenneUnmarks
open SourceClock SourceProfile MersenneSource MersenneDecode HierarchicalDecode Profile MersenneOffsets

abbrev AddressType (t h : Nat) := Address (t+2+h)

/-- Full phase modulus is 4P; the source code's reserved holes are 2,3. -/
def phase (t h : Nat) : Nat := 2^(t+2+h+1)

theorem modulus (t h : Nat) : 2^(t+2+h+3)=4*phase t h := by
  unfold phase
  rw [show t+2+h+3=(t+2+h+1)+2 by omega,Nat.pow_add]
  omega

theorem phase_four {t h : Nat} (hroom : 1≤t+h) : 16≤phase t h := by
  change 2^4≤2^(t+2+h+1)
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem phase_div {t h : Nat} (hroom : 1≤t+h) : 16∣phase t h := by
  change 2^4∣2^(t+2+h+1)
  exact Nat.pow_dvd_pow 2 (by omega)

/-- Every even cyclic shift preserves the actual clock parity. -/
theorem shifted_parity {M : Nat} (hm : 0<M) (hd : 2∣M) (x delta : Nat)
    (he : delta%2=0) : shiftedResidue M delta x%2=x%2 := by
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hb := Nat.mod_lt delta hm
  have he' : delta%M%2=0 := by rw [Nat.mod_mod_of_dvd _ hd]; exact he
  simp only [shiftedResidue,Nat.mod_mod_of_dvd _ hd]
  omega

/-- The first source bit is common for actual owners, despite different
profile twins, offsets, and exceptional second branches. -/
theorem first_common {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (d : Nat) (he : d%2=0) (a rho : AddressType t h)
    (ha : Slots C t h S ho epsilon v d a)
    (hr : Slots C t h S ho false v 0 rho) : a ⟨0,by omega⟩=rho ⟨0,by omega⟩ := by
  have hc := lower_prefix_common (by omega) C (t+2) h 0 (by omega)
    (by decide : 2∣lengthPower (2^2) 0) S S ho ho epsilon false a rho
    (fun _ hi => by omega) v
  have hd : 2∣2^(t+2+h+3) := by
    change 2^1∣2^(t+2+h+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hpa := shifted_parity (Nat.two_pow_pos _) hd
    ((clock (by omega) C (t+2) h S ho epsilon a).position v).val d he
  have hpr := shifted_parity (Nat.two_pow_pos _) hd
    ((clock (by omega) C (t+2) h S ho false rho).position v).val 0 rfl
  have hv : value C t h S ho epsilon v d a%2=value C t h S ho false v 0 rho%2 :=
    hpa.trans (hc.trans hpr.symm)
  exact ha.1.trans ((bit_congr (n:=0) hv).trans hr.1.symm)

def Unmarked {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (epsilon : Bool) (j : Fin 4) (address : AddressType t h) : Prop :=
  Slots C t h S ho epsilon v (delta (phase t h) epsilon j) address ∧
  value C t h S ho epsilon v (delta (phase t h) epsilon j) address%16=
    (value C t h S ho epsilon v (delta (phase t h) epsilon j) address)%2+2*epsilon.toNat

/-- Raw actual low clock values are shared by all candidate owners. -/
theorem owner_low_common {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (d : Nat) (he : d%2=0) (a rho : AddressType t h)
    (ha : Slots C t h S ho epsilon v d a)
    (hr : Slots C t h S ho false v 0 rho) :
    value C t h S ho epsilon v 0 a%16=value C t h S ho false v 0 rho%16 := by
  apply value_low_four_cross
where
  value_low_four_cross : value C t h S ho epsilon v 0 a%16=value C t h S ho false v 0 rho%16 := by
    have hp : AgreeBelow 1 a rho := by
      intro i hi
      have hi0 : i=⟨0,by omega⟩ := Fin.ext (by change i.val=0; omega)
      rw [hi0]
      exact first_common C t h S ho epsilon v d he a rho ha hr
    have hc := actual_low_four C (t+2) h (by omega) S S ho ho epsilon false a rho hp v
    exact SourceStability.shifted_congr (Nat.two_pow_pos _) (by
      change 2^4∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)) 0 0 _ _ rfl hc


theorem zero_shift_mod {M Q : Nat} (hd : Q∣M) (x : Nat) :
    shiftedResidue M 0 x%Q=x%Q := by
  simp only [shiftedResidue,Nat.zero_mod,Nat.sub_zero,Nat.add_mod_right,
    Nat.mod_mod_of_dvd _ hd]

/-- Changing shift keeps the actual raw clock; low congruence at shift zero
therefore transports with every borrow retained. -/
theorem shift_low {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (epsilon : Bool) (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (d x : Nat) (a : AddressType t h)
    (hc : value C t h S ho epsilon v 0 a%16=x%16) :
    value C t h S ho epsilon v d a%16=shiftedResidue (2^(t+2+h+3)) d x%16 := by
  have hd : 16∣2^(t+2+h+3) := by
    change 2^4∣2^(t+2+h+3); exact Nat.pow_dvd_pow 2 (by omega)
  apply SourceStability.shifted_congr (Nat.two_pow_pos _) hd d d _ _ rfl
  exact (zero_shift_mod hd _).symm.trans hc

theorem unmarked_iff_tag {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (hroom : 1≤t+h)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (epsilon : Bool) (j : Fin 4) (a rho : AddressType t h)
    (ha : Slots C t h S ho epsilon v (delta (phase t h) epsilon j) a)
    (hr : Slots C t h S ho false v 0 rho) :
    Unmarked C t h S ho v epsilon j a ↔
      (tag epsilon j).val=(value C t h S ho false v 0 rho)%16/2 := by
  let x := value C t h S ho false v 0 rho
  let d := delta (phase t h) epsilon j
  have hp := phase_four hroom
  have hd := phase_div hroom
  have he : d%2=0 := delta_even hp epsilon j
  have hc := owner_low_common C t h S ho epsilon v d he a rho ha hr
  have hs := shift_low C t h S ho epsilon v d x a hc
  rw [modulus] at hs
  have hpar : value C t h S ho epsilon v d a%2=x%2 := by
    have hh := congrArg (fun z=>z%2) hs
    simp only [Nat.mod_mod_of_dvd _ (by decide : 2∣16)] at hh
    exact hh.trans (shifted_parity (by omega) (by omega) x d he)
  change (Slots C t h S ho epsilon v d a ∧
    value C t h S ho epsilon v d a%16=value C t h S ho epsilon v d a%2+2*epsilon.toNat) ↔ _
  rw [and_iff_right ha,hs,hpar]
  exact low_iff_tag hp hd x epsilon j

/-- Exactly one actual source/profile factor and one disagreement offset
unmarks every physical vertex, uniformly in the full source depth. -/
theorem unique_unmark {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (hroom : 1≤t+h)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    ∃epsilon j a, Unmarked C t h S ho v epsilon j a ∧
      ∀epsilon' j' a', Unmarked C t h S ho v epsilon' j' a' →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨rho,hr,_⟩ := unique_slots C t h S ho false v 0 rfl
  let x := value C t h S ho false v 0 rho
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  have he := delta_even (phase_four hroom) c.1 c.2
  obtain ⟨a,ha,hu⟩ := unique_slots C t h S ho c.1 v (delta (phase t h) c.1 c.2) he
  have hm := (unmarked_iff_tag C t h hroom S ho v c.1 c.2 a rho ha hr).mpr
    (congrArg Fin.val hc)
  refine ⟨c.1,c.2,a,hm,?_⟩
  intro epsilon' j' a' hm'
  have ht := (unmarked_iff_tag C t h hroom S ho v epsilon' j' a' rho hm'.1 hr).mp hm'
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

#print axioms unique_unmark
#print axioms unmarked_iff_tag
#print axioms owner_low_common
end ErdePaths.MersenneUnmarks
