import ErdePaths.Profile
import ErdePaths.Subdivision

namespace ErdePaths.Parameters

/-- Strip the entire power of two, uniformly for every positive length. -/
theorem odd_part (ℓ : Nat) (hℓ : 0<ℓ) :
    ∃ d b, 0<d ∧ d%2=1 ∧ ℓ=d*2^b := by
  by_cases ho : ℓ%2=1
  · exact ⟨ℓ,0,hℓ,ho,by simp⟩
  · have he : ℓ%2=0 := by have := Nat.mod_lt ℓ (by decide : 0<2); omega
    have hsmall : ℓ/2<ℓ := by omega
    have hhalf : 0<ℓ/2 := by omega
    obtain ⟨d,b,hd,ho,hb⟩ := odd_part (ℓ/2) hhalf
    refine ⟨d,b+1,hd,ho,?_⟩
    rw [Nat.pow_succ,←Nat.mul_assoc,←hb]
    omega
termination_by ℓ

theorem odd_divisor_dimension {n ℓ d b : Nat} (hodd : d%2=1) (hlen : ℓ=d*2^b)
    (hdiv : ℓ∣n*2^(n-1)) : d∣n := by
  have hdℓ : d∣ℓ := hlen ▸ Nat.dvd_mul_right d (2^b)
  have hd := Nat.dvd_trans hdℓ hdiv
  exact (Profile.odd_coprime_power_two hodd (n-1)).dvd_of_dvd_mul_right hd

theorem dimension_multiplier {n d : Nat} (hn : 2≤n) (heven : n%2=0)
    (_hd : 0<d) (hodd : d%2=1) (hdiv : d∣n) : ∃ m, 1≤m ∧ n=2*m*d := by
  obtain ⟨k,hk⟩ := hdiv
  have hk0 : 0<k := by
    by_cases hz : k=0
    · rw [hz,Nat.mul_zero] at hk
      omega
    · omega
  have hke : k%2=0 := by
    have hh := congrArg (fun x => x%2) hk
    rw [Nat.mul_mod,hodd,Nat.one_mul,Nat.mod_mod,heven] at hh
    exact hh.symm
  have hk2 : k=2*(k/2) := by omega
  refine ⟨k/2,by omega,?_⟩
  calc
    n=d*k := hk
    _=d*(2*(k/2)) := congrArg (fun x => d*x) hk2
    _=2*(k/2)*d := Nat.mul_comm _ _

theorem exponent_bound {n ℓ d b : Nat} (hd : 0<d) (hlen : ℓ=d*2^b)
    (hlt : ℓ<2^n) : b≤n-d.log2-1 := by
  have hlo : 2^d.log2≤d := (Nat.le_log2 (by omega : d≠0)).mp (Nat.le_refl _)
  have hp : 2^(d.log2+b)<2^n := by
    rw [Nat.pow_add]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2^b) hlo) (hlen ▸ hlt)
  have hexp : d.log2+b<n := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hp
  omega

/-- Exact canonical frontier divisor; no admissible power-of-two exponent
or odd binary complexity is omitted. -/
theorem frontier_divides {n ℓ d b : Nat} (hd : 0<d) (hlen : ℓ=d*2^b)
    (hlt : ℓ<2^n) : ℓ∣d*2^(n-d.log2-1) := by
  have hb := exponent_bound hd hlen hlt
  refine ⟨2^(n-d.log2-1-b),?_⟩
  rw [hlen,Nat.mul_assoc,←Nat.pow_add,Nat.add_sub_of_le hb]

/-- Every admissible parameter pair belongs to the SAME odd-frontier route. -/
theorem normalize {n ℓ : Nat} (hn : 2≤n) (heven : n%2=0) (hℓ : 1≤ℓ)
    (hlt : ℓ<2^n) (hdiv : ℓ∣n*2^(n-1)) :
    ∃ m d b, 1≤m ∧ 0<d ∧ d%2=1 ∧ n=2*m*d ∧ ℓ=d*2^b ∧
      b≤n-d.log2-1 ∧ ℓ∣d*2^(n-d.log2-1) := by
  obtain ⟨d,b,hd,ho,he⟩ := odd_part ℓ (by omega)
  obtain ⟨m,hm,hnm⟩ := dimension_multiplier hn heven hd ho (odd_divisor_dimension ho he hdiv)
  exact ⟨m,d,b,hm,hd,ho,hnm,he,exponent_bound hd he hlt,frontier_divides hd he hlt⟩

/-- Final arithmetic/subdivision assembly. This is conditional on the actual
uniform frontier construction, not an unconditional conjecture theorem. -/
theorem target_from_odd_frontiers
    (frontiers : ∀ m d, 1≤m → 0<d → d%2=1 →
      HasPathDecomposition (2*m*d) (d*2^(2*m*d-d.log2-1))) :
    ErdeEvenHypercubeConjecture := by
  intro n ℓ hn heven hℓ hlt hdiv
  obtain ⟨m,d,b,hm,hd,ho,hnm,he,hb,hfront⟩ := normalize hn heven hℓ hlt hdiv
  have hf : HasPathDecomposition n (d*2^(n-d.log2-1)) := by
    rw [hnm]
    exact frontiers m d hm hd ho
  exact subdivision hf hℓ hfront

#print axioms normalize
#print axioms target_from_odd_frontiers
end ErdePaths.Parameters
