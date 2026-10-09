import ErdePaths.MersenneDecode

namespace ErdePaths.MersenneOffsets
open SourceProfile HierarchicalDecode SourceClock

/-- The literal four disagreement positions of the uniform long turn word. -/
def bad (P : Nat) (j : Fin 4) : Nat :=
  if j.val=0 then P-2 else if j.val=1 then P+2
  else if j.val=2 then P+3 else 2*P-1

/-- Reverse and forward unmark offsets in the actual phase modulus 4P. -/
def delta (P : Nat) (epsilon : Bool) (j : Fin 4) : Nat :=
  if epsilon then 2*bad P j else 4*P-2*bad P j

def tag (epsilon : Bool) (j : Fin 4) : Fin 8 :=
  if epsilon then
    if j.val=0 then 7 else if j.val=1 then 3 else if j.val=2 then 4 else 0
  else
    if j.val=0 then 2 else if j.val=1 then 6 else if j.val=2 then 5 else 1

theorem tag_bijection :
    (∀q : Fin 8, ∃c : Bool×Fin 4, tag c.1 c.2=q) ∧
    (∀c d : Bool×Fin 4, tag c.1 c.2=tag d.1 d.2 → c=d) := by
  simp only [Prod.forall,Prod.exists]
  decide

theorem bad_bound {P : Nat} (hp : 16≤P) (j : Fin 4) : bad P j<2*P := by
  unfold bad
  split <;> (try split) <;> (try split) <;> omega

theorem delta_bound {P : Nat} (hp : 16≤P) (epsilon : Bool) (j : Fin 4) :
    delta P epsilon j<4*P := by
  have hb := bad_bound hp j
  have hpos : 0<bad P j := by
    unfold bad
    split <;> (try split) <;> (try split) <;> omega
  cases epsilon <;> simp only [delta,Bool.false_eq_true,↓reduceIte] <;> omega

theorem delta_even {P : Nat} (hp : 16≤P) (epsilon : Bool) (j : Fin 4) :
    delta P epsilon j%2=0 := by
  have hb := bad_bound hp j
  cases epsilon <;> simp only [delta,Bool.false_eq_true,↓reduceIte] <;> omega

/-- All eight residue classes are derived for arbitrary P divisible by16;
only the fixed four-position lookup is finite. -/
theorem combined_residue {P : Nat} (hp : 16≤P) (hd : 16∣P)
    (epsilon : Bool) (j : Fin 4) :
    (delta P epsilon j+2*epsilon.toNat)%16=2*(tag epsilon j).val := by
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hj := j.isLt
  cases epsilon <;> simp only [delta,tag,Bool.toNat_false,Bool.toNat_true,
    Bool.false_eq_true,↓reduceIte]
  all_goals
    unfold bad
    by_cases h0 : j.val=0
    · simp [h0]; omega
    · by_cases h1 : j.val=1
      · simp [h0,h1]; omega
      · by_cases h2 : j.val=2
        · simp [h0,h1,h2]; omega
        · simp [h0,h1,h2]; omega

/-- Low profile/hole equality is exactly the eight-way offset lookup. -/
theorem low_iff_tag {P : Nat} (hp : 16≤P) (hd : 16∣P)
    (x : Nat) (epsilon : Bool) (j : Fin 4) :
    shiftedResidue (4*P) (delta P epsilon j) x%16=x%2+2*epsilon.toNat ↔
      (tag epsilon j).val=x%16/2 := by
  have hb := delta_bound hp epsilon j
  have hc := combined_residue hp hd epsilon j
  have hz := Nat.mod_eq_zero_of_dvd hd
  have ht := (tag epsilon j).isLt
  have he : epsilon.toNat≤1 := by cases epsilon <;> decide
  have hdiv : 16∣4*P := Nat.dvd_mul_left_of_dvd hd 4
  simp only [shiftedResidue,Nat.mod_eq_of_lt hb,Nat.mod_mod_of_dvd _ hdiv]
  have hrem : x%16%2=x%2 := Nat.mod_mod_of_dvd _ (by decide)
  omega

theorem unique_low {P : Nat} (hp : 16≤P) (hd : 16∣P) (x : Nat) :
    ∃c : Bool×Fin 4,
      shiftedResidue (4*P) (delta P c.1 c.2) x%16=x%2+2*c.1.toNat ∧
      ∀d : Bool×Fin 4,
        shiftedResidue (4*P) (delta P d.1 d.2) x%16=x%2+2*d.1.toNat → d=c := by
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  refine ⟨c,(low_iff_tag hp hd x c.1 c.2).mpr (congrArg Fin.val hc),?_⟩
  intro d hd'
  apply tag_bijection.2 d c
  apply Fin.ext
  exact ((low_iff_tag hp hd x d.1 d.2).mp hd').trans (congrArg Fin.val hc).symm

#print axioms unique_low
#print axioms combined_residue
end ErdePaths.MersenneOffsets
