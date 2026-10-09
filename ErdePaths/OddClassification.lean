import ErdePaths.Parameters

namespace ErdePaths.OddClassification

private theorem pow_even {r : Nat} (hr : 1≤r) : 2^r%2=0 := by
  have he : r=(r-1)+1 := by omega
  rw [he,Nat.pow_succ]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

/-- Every positive odd part is either one, has two binary ones, or belongs
 to the same arbitrary-depth P+L+b construction. -/
theorem classify {d : Nat} (hd : 0<d) (ho : d%2=1) :
    d=1 ∨
    (∃R, 1≤R ∧ d=2^R+1 ∧ d.log2=R) ∨
    (∃R s b, 1≤s ∧ s<R ∧ 0<b ∧ b<2^s ∧ b%2=1 ∧
      d=2^R+2^s+b ∧ d.log2=R) := by
  by_cases h1 : d=1
  · exact Or.inl h1
  have hd3 : 3≤d := by omega
  let R := d.log2
  have hR : 1≤R := (Nat.le_log2 (by omega : d≠0)).mpr (by omega)
  have hp : 2^R≤d := Nat.log2_self_le (by omega)
  have htop : d<2^(R+1) := Nat.lt_log2_self
  have he := pow_even hR
  let t := d-2^R
  have ht : d=2^R+t := by dsimp only [t]; omega
  have hto : t%2=1 := by
    have hh := congrArg (fun k=>k%2) ht
    rw [Nat.add_mod,he,Nat.zero_add,Nat.mod_mod,ho] at hh
    exact hh.symm
  have htpos : 0<t := by omega
  have htbound : t<2^R := by rw [Nat.pow_succ] at htop; omega
  by_cases ht1 : t=1
  · exact Or.inr (Or.inl ⟨R,hR,by omega,rfl⟩)
  have ht3 : 3≤t := by omega
  let s := t.log2
  have hs : 1≤s := (Nat.le_log2 (by omega : t≠0)).mpr (by omega)
  have hsR : s<R := (Nat.log2_lt (by omega : t≠0)).mpr htbound
  have hps : 2^s≤t := Nat.log2_self_le (by omega)
  have hts : t<2^(s+1) := Nat.lt_log2_self
  let b := t-2^s
  have htb : t=2^s+b := by dsimp only [b]; omega
  have hbe : 2^s%2=0 := pow_even hs
  have hbo : b%2=1 := by
    have hh := congrArg (fun k=>k%2) htb
    rw [Nat.add_mod,hbe,Nat.zero_add,Nat.mod_mod,hto] at hh
    exact hh.symm
  have hbpos : 0<b := by omega
  have hb : b<2^s := by rw [Nat.pow_succ] at hts; omega
  exact Or.inr (Or.inr ⟨R,s,b,hs,hsR,hbpos,hb,hbo,by omega,rfl⟩)

/-- Exactly the opening split for the generic higher-weight construction:
A>=4, the isolated anti turn, or the complementary Mersenne word. -/
theorem opening_split {R s b : Nat} (hsR : s<R) (hb : b<2^s) (ho : b%2=1) :
    2≤R-s ∨ (R-s=1 ∧ b≤2^s-3) ∨ (R-s=1 ∧ b=2^s-1) := by
  have hr : 1≤R-s := by omega
  by_cases h2 : 2≤R-s
  · exact Or.inl h2
  have he : R-s=1 := by omega
  by_cases hm : b=2^s-1
  · exact Or.inr (Or.inr ⟨he,hm⟩)
  by_cases hz : s=0
  · subst s
    simp only [Nat.pow_zero] at hb
    omega
  · have hp := pow_even (show 1≤s by omega)
    exact Or.inr (Or.inl ⟨he,by omega⟩)

/-- Exact highest bit of the literal ordinary construction coefficient. -/
theorem coefficient_log2 {R s b : Nat} (hsR : s<R) (hb : b<2^s) :
    (2^R+2^s+b).log2=R := by
  have hp := Nat.two_pow_pos R
  apply (Nat.log2_eq_iff (by omega)).mpr
  constructor
  · omega
  · have hs : 2^(s+1)≤2^R := Nat.pow_le_pow_right (by decide : 1≤2) (by omega)
    rw [Nat.pow_succ] at hs ⊢
    omega

/-- Exact highest bit of the complementary coefficient at every depth. -/
theorem mersenne_log2 {R : Nat} (_hR : 1≤R) : (2^(R+1)-1).log2=R := by
  have hp := Nat.two_pow_pos R
  have he : 2^(R+1)=2^R*2 := Nat.pow_succ _ _
  apply (Nat.log2_eq_iff (by omega)).mpr
  constructor <;> omega

/-- The only higher-weight parameter below the ordinary room is d=7. -/
theorem small_ordinary {R s b : Nat} (hs : 1≤s) (hsR : s<R)
    (hb : b<2^s) (ho : b%2=1) (hR : R<3) :
    R=2 ∧ s=1 ∧ b=1 ∧ 2^R+2^s+b=7 := by
  have hRs : R=2 ∧ s=1 := by omega
  rcases hRs with ⟨rfl,rfl⟩
  change b<2 at hb
  have hb1 : b=1 := by omega
  subst b
  decide

/-- The complementary room's only additional boundary is d=15. -/
theorem small_mersenne {R : Nat} (hR : 3≤R) (hsmall : R<4) :
    R=3 ∧ 2^(R+1)-1=15 := by
  have he : R=3 := by omega
  subst R
  decide

#print axioms coefficient_log2
#print axioms mersenne_log2
#print axioms classify
#print axioms opening_split
end ErdePaths.OddClassification
