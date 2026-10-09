import ErdePaths.ZeroUpperCodeOrigins
import ErdePaths.MersennePhysicalIncidence
import ErdePaths.MersenneReciprocalMulticover

namespace ErdePaths.ZeroUpperIncidence
open SourceClock SourceProfile HierarchicalDecode MersenneOffsets Profile
attribute [local instance] Classical.propDecidable

theorem bad_bound8 {P : Nat} (hp : 8≤P) (j : Fin 4) : bad P j<2*P := by
  unfold bad
  split <;> (try split) <;> (try split) <;> omega

theorem delta_bound8 {P : Nat} (hp : 8≤P) (epsilon : Bool) (j : Fin 4) :
    delta P epsilon j<4*P := by
  have hb := bad_bound8 hp j
  have hpos : 0<bad P j := by
    unfold bad
    split <;> (try split) <;> (try split) <;> omega
  cases epsilon <;> simp only [delta,Bool.false_eq_true,↓reduceIte] <;> omega

theorem delta_even8 {P : Nat} (hp : 8≤P) (epsilon : Bool) (j : Fin 4) :
    delta P epsilon j%2=0 := by
  have hb := bad_bound8 hp j
  cases epsilon <;> simp only [delta,Bool.false_eq_true,↓reduceIte] <;> omega

/-- All eight residue classes are derived for arbitrary P divisible by8;
only the fixed four-position lookup is finite. -/
theorem combined_residue8 {P : Nat} (hp : 8≤P) (hd : 8∣P)
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
theorem low_iff_tag8 {P : Nat} (hp : 8≤P) (hd : 8∣P)
    (x : Nat) (epsilon : Bool) (j : Fin 4) :
    shiftedResidue (4*P) (delta P epsilon j) x%16=x%2+2*epsilon.toNat ↔
      (tag epsilon j).val=x%16/2 := by
  have hb := delta_bound8 hp epsilon j
  have hc := combined_residue8 hp hd epsilon j
  have hz := Nat.mod_eq_zero_of_dvd hd
  have ht := (tag epsilon j).isLt
  have he : epsilon.toNat≤1 := by cases epsilon <;> decide
  have hdiv : 16∣4*P := by obtain ⟨q,hq⟩ := hd; subst P; exact ⟨2*q,by omega⟩
  simp only [shiftedResidue,Nat.mod_eq_of_lt hb,Nat.mod_mod_of_dvd _ hdiv]
  have hrem : x%16%2=x%2 := Nat.mod_mod_of_dvd _ (by decide)
  omega

theorem unique_low8 {P : Nat} (hp : 8≤P) (hd : 8∣P) (x : Nat) :
    ∃c : Bool×Fin 4,
      shiftedResidue (4*P) (delta P c.1 c.2) x%16=x%2+2*c.1.toNat ∧
      ∀d : Bool×Fin 4,
        shiftedResidue (4*P) (delta P d.1 d.2) x%16=x%2+2*d.1.toNat → d=c := by
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  refine ⟨c,(low_iff_tag8 hp hd x c.1 c.2).mpr (congrArg Fin.val hc),?_⟩
  intro d hd'
  apply tag_bijection.2 d c
  apply Fin.ext
  exact ((low_iff_tag8 hp hd x d.1 d.2).mp hd').trans (congrArg Fin.val hc).symm



section Small
open MersenneUnmarks MersenneDecode
theorem small_unmarked_iff_tag {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h)
    (epsilon : Bool) (j : Fin 4) (a rho : AddressType t h)
    (ha : Slots C t h S ho epsilon v (delta (phase t h) epsilon j) a)
    (hr : Slots C t h S ho false v 0 rho) :
    Unmarked C t h S ho v epsilon j a ↔
      (tag epsilon j).val=(value C t h S ho false v 0 rho)%16/2 := by
  let x := value C t h S ho false v 0 rho
  let d := delta (phase t h) epsilon j
  have hp : 8≤phase t h := Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 3≤t+2+h+1)
  have hd : 8∣phase t h := Nat.pow_dvd_pow 2 (by omega : 3≤t+2+h+1)
  have he : d%2=0 := delta_even8 hp epsilon j
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
  exact low_iff_tag8 hp hd x epsilon j

/-- Exactly one actual source/profile factor and one disagreement offset
unmarks every physical vertex, uniformly in the full source depth. -/
theorem small_unique_unmark {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    ∃epsilon j a, Unmarked C t h S ho v epsilon j a ∧
      ∀epsilon' j' a', Unmarked C t h S ho v epsilon' j' a' →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨rho,hr,_⟩ := unique_slots C t h S ho false v 0 rfl
  let x := value C t h S ho false v 0 rho
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  have he := delta_even8 (show 8≤phase t h from Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 3≤t+2+h+1)) c.1 c.2
  obtain ⟨a,ha,hu⟩ := unique_slots C t h S ho c.1 v (delta (phase t h) c.1 c.2) he
  have hm := (small_unmarked_iff_tag C t h S ho v c.1 c.2 a rho ha hr).mpr
    (congrArg Fin.val hc)
  refine ⟨c.1,c.2,a,hm,?_⟩
  intro epsilon' j' a' hm'
  have ht := (small_unmarked_iff_tag C t h S ho v epsilon' j' a' rho hm'.1 hr).mp hm'
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


end Small

section SmallCode
open MersenneUnmarks MersenneDecode MersenneCode
theorem small_unique_code_owner {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    ∃epsilon j a,
      value C t h S ho epsilon v (MersenneOffsets.delta (phase t h) epsilon j) a=
        (code (by omega) true epsilon a).val ∧
      ∀epsilon' j' a',
        value C t h S ho epsilon' v (MersenneOffsets.delta (phase t h) epsilon' j') a'=
          (code (by omega) true epsilon' a').val →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨epsilon,j,a,hm,hu⟩ := small_unique_unmark C t h S ho v
  refine ⟨epsilon,j,a,(unmarked_iff_code C t h S ho v epsilon j a).mp hm,?_⟩
  intro epsilon' j' a' hc
  exact hu epsilon' j' a' ((unmarked_iff_code C t h S ho v epsilon' j' a').mpr hc)


end SmallCode

section Large
open MersenneLargeUnmarks MersenneLargeDecode
open MersenneUnmarks (shifted_parity)
theorem large_unmarked_iff_tag {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h)
    (epsilon : Bool) (j : Fin 4) (a rho : AddressType k h)
    (ha : Slots hebase C k h hk S ho epsilon v (delta (phase k h) epsilon j) a)
    (hr : Slots hebase C k h hk S ho false v 0 rho) :
    Unmarked hebase C k h hk S ho v epsilon j a ↔
      (tag epsilon j).val=(value hebase C k h S ho false v 0 rho)%16/2 := by
  let x := value hebase C k h S ho false v 0 rho
  let d := delta (phase k h) epsilon j
  have hp : 8≤phase k h := Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 3≤k+h+1)
  have hd : 8∣phase k h := Nat.pow_dvd_pow 2 (by omega : 3≤k+h+1)
  have he : d%2=0 := delta_even8 hp epsilon j
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
  exact low_iff_tag8 hp hd x epsilon j

/-- Exactly one actual source/profile factor and one disagreement offset
unmarks every physical vertex, uniformly in the full source depth. -/
theorem large_unique_unmark {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e)) (k h : Nat) (hk : 2≤k)
    (S : Address (k)→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (k)×VertexPower V (k)) h) :
    ∃epsilon j a, Unmarked hebase C k h hk S ho v epsilon j a ∧
      ∀epsilon' j' a', Unmarked hebase C k h hk S ho v epsilon' j' a' →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨rho,hr,_⟩ := unique_slots hebase C k h hk S ho false v 0
  let x := value hebase C k h S ho false v 0 rho
  let q : Fin 8 := ⟨x%16/2,by have := Nat.mod_lt x (by decide : 0<16); omega⟩
  obtain ⟨c,hc⟩ := tag_bijection.1 q
  have he := delta_even8 (show 8≤phase k h from Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 3≤k+h+1)) c.1 c.2
  obtain ⟨a,ha,hu⟩ := unique_slots hebase C k h hk S ho c.1 v (delta (phase k h) c.1 c.2)
  have hm := (large_unmarked_iff_tag hebase C k h hk S ho v c.1 c.2 a rho ha hr).mpr
    (congrArg Fin.val hc)
  refine ⟨c.1,c.2,a,hm,?_⟩
  intro epsilon' j' a' hm'
  have ht := (large_unmarked_iff_tag hebase C k h hk S ho v epsilon' j' a' rho hm'.1 hr).mp hm'
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

theorem large_unique_code_owner {V : Type} {e : Nat} (hebase : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ∃epsilon j a,
      value hebase C k h S ho epsilon v (delta (phase k h) epsilon j) a=
        (MersenneCode.code (by omega) false epsilon a).val ∧
      ∀epsilon' j' a',
        value hebase C k h S ho epsilon' v (delta (phase k h) epsilon' j') a'=
          (MersenneCode.code (by omega) false epsilon' a').val →
        epsilon'=epsilon ∧ j'=j ∧ a'=a := by
  obtain ⟨epsilon,j,a,hm,hu⟩ := large_unique_unmark hebase C k h hk S ho v
  refine ⟨epsilon,j,a,(unmarked_iff_code hebase C k h hk S ho v epsilon j a).mp hm,?_⟩
  intro epsilon' j' a' hc
  exact hu epsilon' j' a' ((unmarked_iff_code hebase C k h hk S ho v epsilon' j' a').mpr hc)


end Large

section Counts
open MersenneComplement DenseSourceCounts DenseSourceMarks
theorem removed_eligible {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional epsilon : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) (a : Address (k+h))
    (hm : Removed he C k h hk S ho exceptional epsilon v a) :
    Eligible he C k h hk S ho epsilon v a := by
  obtain ⟨j,hj⟩ := hm
  have hp : 8≤2^(k+h+1) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  have hd := delta_even8 hp epsilon j
  have hs := SourceParity.even_shift_bit (Nat.two_pow_pos (k+h+3))
    (show 2∣2^(k+h+3) by change 2^1∣2^(k+h+3); exact Nat.pow_dvd_pow 2 (by omega))
    (MersenneOffsets.delta (2^(k+h+1)) epsilon j)
    ((clock he C k h S ho epsilon a).position v).val hd
  have hc := congrFun (MersenneCode.code_bits (by omega : 2≤k+h) exceptional epsilon a) ⟨0,by omega⟩
  simp only [binaryTuple,MersenneCode.codeBits,↓reduceIte] at hc
  have hb := congrArg (fun n => n.testBit 0) hj
  exact hs.symm.trans (hb.trans hc)

private theorem count_unique {X : Type} [DecidableEq X] (l : List X) (hn : l.Nodup)
    (p : X→Bool) (owner : X) (hp : ∀ x∈l, p x=true ↔ x=owner) :
    l.countP p=if owner∈l then 1 else 0 := by
  classical
  have hc : l.countP p=l.count owner := by
    apply List.countP_congr
    intro x hx
    simpa only [beq_iff_eq] using hp x hx
  exact hc.trans hn.count

private theorem count_remove {X : Type} (l : List X) (E R : X→Prop)
    (sub : ∀x, R x→E x) :
    l.countP (fun x => decide (E x ∧ ¬R x))+l.countP (fun x => decide (R x))=
      l.countP (fun x => decide (E x)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases he : E x <;> by_cases hr : R x <;> simp_all <;> omega

private theorem retained_count {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀a, cardinality (S a)%2=1) (exceptional : Bool)
    (v : VertexPower (VertexPower V k×VertexPower V k) h)
    (owner : ∃b a, Removed he C k h hk S ho exceptional b v a ∧
      ∀b' a', Removed he C k h hk S ho exceptional b' v a'→b'=b ∧ a'=a) :
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q)))=2^(k+h)-1 := by
  classical
  obtain ⟨b,a,hm,hu⟩ := owner
  let q0 := DenseSourceMarks.code 1 (show 1<k+h+1 by omega) b a
  have hp (q : Vertex (k+h+1)) : Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q) ↔ q=q0 := by
    constructor
    · intro hq
      obtain ⟨hb,ha⟩ := hu _ _ hq
      rw [←code_of 1 (by omega) q,hb,ha]
    · intro hq
      subst q
      simpa only [q0,epsilon_of_code,address_of_code] using hm
  have hr : (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q)))=1 := by
    have hc := count_unique (List.finRange _) (List.nodup_finRange _)
      (fun q => decide (Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))) q0
      (by intro q hq; simp only [decide_eq_true_eq]; exact hp q)
    simpa only [List.mem_finRange,ite_true] using hc
  have hh := count_remove (List.finRange (2^(k+h+1)))
    (fun q => Eligible he C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q))
    (fun q => Removed he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q))
    (fun q hm => removed_eligible he C k h hk S ho exceptional (epsilonOf 1 q) v (addressOf 1 q) hm)
  rw [hr,eligible_count] at hh
  have hs := congrArg (fun n : Nat => n-1) hh
  simp only [Nat.add_sub_cancel] at hs
  apply Eq.trans ?_ hs
  apply List.countP_congr
  intro q hq
  simp only [decide_eq_true_eq]

/-- Actual exceptional unmark construction supplies the sole removal. -/
theorem small_retained_count {V : Type} (C : ClockData V (2^2)) (t h : Nat)
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool)
    (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    (List.finRange (2^(t+2+h+1))).countP (fun q => decide
      (Eligible (by omega) C (t+2) h (by omega) S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed (by omega) C (t+2) h (by omega) S ho true (epsilonOf 1 q) v (addressOf 1 q)))=2^(t+2+h)-1 := by
  apply retained_count (by omega) C (t+2) h (by omega) S ho true v
  obtain ⟨b,j,a,hm,hu⟩ := small_unique_code_owner C t h S ho v
  refine ⟨b,a,⟨j,hm⟩,?_⟩
  intro b' a' hm'
  obtain ⟨j',hj'⟩ := hm'
  obtain ⟨hb,_,ha⟩ := hu b' j' a' hj'
  exact ⟨hb,ha⟩

/-- Actual larger-base raw unmark construction supplies the sole removal. -/
theorem large_retained_count {V : Type} {e : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, cardinality (S a)%2=1)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (List.finRange (2^(k+h+1))).countP (fun q => decide
      (Eligible (by omega) C k h hk S ho (epsilonOf 1 q) v (addressOf 1 q) ∧
       ¬Removed (by omega) C k h hk S ho false (epsilonOf 1 q) v (addressOf 1 q)))=2^(k+h)-1 := by
  apply retained_count (by omega) C k h hk S ho false v
  obtain ⟨b,j,a,hm,hu⟩ := large_unique_code_owner he C k h hk S ho v
  refine ⟨b,a,⟨j,hm⟩,?_⟩
  intro b' a' hm'
  obtain ⟨j',hj'⟩ := hm'
  obtain ⟨hb,_,ha⟩ := hu b' j' a' hj'
  exact ⟨hb,ha⟩


end Counts

namespace Geometric
open SquareLift OrientedClock
private theorem threshold_iff {K : Nat} (_hK : 0<K) (x : Fin (K*2)) (z : Fin 2) :
    (∃i : Fin K, x=AnchoredEmbedding.positionEncode i z) ↔ x.val%2=z.val := by
  have hh := BaselineResidues.threshold_residue_iff (by decide : 0<2) (by decide : 0<1)
    x z (fun _=>True)
  constructor
  · intro hx
    obtain ⟨u,_,hu⟩ := hh.mp (by obtain ⟨i,hi⟩ := hx; exact ⟨i,hi,True.intro⟩)
    have hz : u.val=0 := by have := u.isLt; omega
    simpa only [hz,Nat.mul_zero,Nat.zero_add] using hu
  · intro hx
    obtain ⟨i,hi,_⟩ := hh.mpr ⟨⟨0,by decide⟩,True.intro,by simpa using hx⟩
    exact ⟨i,hi⟩

private theorem bit_zero_iff (n m : Nat) : n.testBit 0=m.testBit 0 ↔ n%2=m%2 := by
  have hn := Nat.mod_lt n (by decide : 0<2)
  have hm := Nat.mod_lt m (by decide : 0<2)
  simp only [Nat.testBit_zero,decide_eq_decide]
  omega

/-- Actual threshold eligibility from the literal full-cycle origin. -/
theorem physical_threshold {U : Type} {K : Nat} (hK : 0<K)
    (C : ClockData U (K*2)) (endpoint : Fin (K*2)) (z : Fin 2) (epsilon : Bool) (v : U) :
    let G := clock (Nat.mul_pos hK (by decide)) C
      (index (Nat.mul_pos hK (by decide)) endpoint (!epsilon) (BaselinePhysical.threshold hK z)) epsilon
    (∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ↔
      (C.position v).val.testBit 0=endpoint.val.testBit 0 := by
  dsimp only
  rw [threshold_iff hK,bit_zero_iff]
  have hh := BaselinePhysical.class_incidence (L:=1) hK (by decide) (by decide)
    (Nat.one_dvd K) C endpoint ⟨endpoint.val%2,Nat.mod_lt _ (by decide)⟩ rfl z epsilon v ⟨0,by decide⟩
  have hz : SourceStability.signedOffset 2 2 0 (!epsilon)=0 := by
    cases epsilon <;> simp [SourceStability.signedOffset,shiftedResidue]
  simpa only [Nat.mul_one,Nat.mul_zero,Nat.zero_add,hz,shiftedResidue,Nat.zero_mod,
    Nat.sub_zero,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod] using hh

private theorem exponent_room (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega

private theorem coarse_div {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponent_room (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have hd : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 hd

noncomputable def orientedSource {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (exceptional : Bool)
    (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a)
    (epsilon : Bool) (a : Address (k+h)) (z : Fin 2) :
    ClockData (VertexPower (VertexPower V k×VertexPower V k) h)
      (2^(e*2^(k+h+1)-1)*2) :=
  let D := origins a
  let raw := castClock (SourceLengths.fine_length he k h 1 (by omega))
    (SourceProfile.clock he C k h S ho epsilon a)
  let ep := Fin.cast (SourceLengths.fine_length he k h 1 (by omega))
    (MersenneCodeOrigins.endpoint D epsilon)
  let hK := Nat.two_pow_pos (e*2^(k+h+1)-1)
  clock (Nat.mul_pos hK (by decide)) raw
    (index (Nat.mul_pos hK (by decide)) ep (!epsilon) (BaselinePhysical.threshold hK z)) epsilon

section Source
variable {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
  (exceptional : Bool)
  (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a)
  (epsilon : Bool) (a : Address (k+h)) (z : Fin 2)
local notation "K" => 2^(e*2^(k+h+1)-1)
local notation "periodN" => 2^(k+h+1)
local notation "D" => origins a
local notation "raw" => castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho epsilon a)
local notation "ep" => Fin.cast (SourceLengths.fine_length he k h 1 (by omega)) (MersenneCodeOrigins.endpoint D epsilon)
local notation "G" => orientedSource he C k h hk room S ho exceptional origins epsilon a z

private theorem full_period : 2^(k+h+3)=4*periodN := by
  have ht : k+h+3=(k+h+1)+2 := by omega
  rw [ht,Nat.pow_add]
  simp [Nat.mul_comm]

private theorem endpoint_zero_bit : (ep).val.testBit 0=a ⟨0,by omega⟩ := by
  have hc := MersenneCodeOrigins.endpoint_code D epsilon
  have hb := congrArg (fun n=>n.testBit 0) hc
  have hi : decide (0<k+h+3)=true := by simp
  simp only [Nat.testBit_mod_two_pow,hi,Bool.true_and] at hb
  have ha := congrFun (MersenneCode.code_bits (by omega : 2≤k+h) exceptional epsilon a) ⟨0,by omega⟩
  have ha' : (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a).val.testBit 0=a ⟨0,by omega⟩ := by
    simpa only [binaryTuple,MersenneCode.codeBits,↓reduceIte] using ha
  exact hb.trans ha'

theorem threshold_eligible (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ↔
      MersenneComplement.Eligible he C k h (by omega) S ho epsilon v a := by
  have hh' := physical_threshold (Nat.two_pow_pos _) raw ep z epsilon v
  dsimp only [orientedSource] at hh' ⊢
  rw [endpoint_zero_bit he C k h hk S ho exceptional origins epsilon a] at hh'
  simpa only [MersenneComplement.Eligible,castClock_position,Fin.val_cast] using hh'

theorem unmark_removed (v : VertexPower (VertexPower V k×VertexPower V k) h) (row : Fin B) :
    ((∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z) ∧
      ¬AACMarkIntervals.IsMark (Nat.two_pow_pos _)
        (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row)) ↔
      MersenneComplement.Removed he C k h (by omega) S ho exceptional epsilon v a := by
  have hperiod := full_period k h
  have hc : (ep).val%(4*periodN)=(Fin.cast hperiod (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a)).val := by
    simpa only [Fin.val_cast,←hperiod] using MersenneCodeOrigins.endpoint_code D epsilon
  have hP : 8≤periodN := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  have ht := MersennePhysicalUnmarks.physical_unmarks (Nat.two_pow_pos _) hP (coarse_div he k h)
    raw ep (Fin.cast hperiod (MersenneCode.code (by omega : 2≤k+h) exceptional epsilon a)) hc z epsilon v row
  dsimp only [orientedSource] at ht ⊢
  simpa only [MersenneComplement.Removed,MersenneComplement.RemovedAt,MersenneComplement.rawValue,
    castClock_position,Fin.val_cast,hperiod] using ht

theorem mark_retained (v : VertexPower (VertexPower V k×VertexPower V k) h) (row : Fin B) :
    AACMarkIntervals.IsMark (Nat.two_pow_pos _)
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row) ↔
      MersenneComplement.Eligible he C k h (by omega) S ho epsilon v a ∧
      ¬MersenneComplement.Removed he C k h (by omega) S ho exceptional epsilon v a := by
  have ht := threshold_eligible he C k h hk room S ho exceptional origins epsilon a z v
  have hu := unmark_removed he C k h hk room S ho exceptional origins epsilon a z v row
  have hm : AACMarkIntervals.IsMark (Nat.two_pow_pos _)
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN)) w.1) z ((G).position v,row) →
      ∃i : Fin K, (G).position v=AnchoredEmbedding.positionEncode i z := by
    rintro ⟨i,j,hx,_⟩
    exact ⟨i,(Prod.mk.inj hx).1⟩
  constructor
  · intro hh'
    refine ⟨ht.mp (hm hh'),?_⟩
    intro hr
    exact (hu.mpr hr).2 hh'
  · rintro ⟨he',hn⟩
    apply Classical.byContradiction
    intro hnm
    exact hn (hu.mp ⟨ht.mpr he',hnm⟩)
end Source

/-- Literal geometric incidence across every full numeric configuration.
The actual H row may depend arbitrarily on the configuration. -/
noncomputable def multiplicity {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (exceptional : Bool)
    (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a) (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) : Nat :=
  (List.finRange (2^(k+h+1))).countP (fun q=>decide
    (AACMarkIntervals.IsMark (Nat.two_pow_pos (e*2^(k+h+1)-1))
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
        (TurnPatterns.long (P:=2^(k+h+1))) w.1) z
      ((orientedSource he C k h hk room S ho exceptional origins
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z).position v,rows q)))

theorem multiplicity_retained {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (exceptional : Bool)
    (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a) (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    multiplicity he C k h hk room S ho exceptional origins z rows v=
      (List.finRange (2^(k+h+1))).countP (fun q=>decide
        (MersenneComplement.Eligible he C k h hk S ho (DenseSourceCounts.epsilonOf 1 q) v (DenseSourceCounts.addressOf 1 q) ∧
         ¬MersenneComplement.Removed he C k h hk S ho exceptional (DenseSourceCounts.epsilonOf 1 q) v (DenseSourceCounts.addressOf 1 q))) := by
  apply List.countP_congr
  intro q hq
  simp only [decide_eq_true_eq]
  exact mark_retained he C k h hk room S ho exceptional origins
    (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v (rows q)

/-- Exceptional small-base actual physical long marks have exactly L−1
incidences, derived from the unique actual numeric removal owner. -/
theorem small_multiplicity {V : Type} {B : Nat} (C : ClockData V (2^2)) (t h : Nat)
    (room : 2^(t+2+h+3)∣lengthPower (2^2) (t+2))
    (S : Address (t+2)→Fin (2^(2*2^(t+2)))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (origins : ∀a : Address (t+2+h), MersenneCodeOrigins.Data (by omega) C (t+2) h (by omega) S ho true a)
    (z : Fin 2) (rows : Vertex (t+2+h+1)→Fin B)
    (v : VertexPower (VertexPower V (t+2)×VertexPower V (t+2)) h) :
    multiplicity (by omega) C (t+2) h (by omega) room S ho true origins z rows v=2^(t+2+h)-1 := by
  rw [multiplicity_retained]
  exact ZeroUpperIncidence.small_retained_count C t h S ho v

/-- Larger-base actual physical long marks have the same exact L−1 count
with the ordinary code, uniformly in every hierarchy depth. -/
theorem large_multiplicity {V : Type} {e B : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
    (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
    (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data (by omega) C k h (by omega) S ho false a)
    (z : Fin 2) (rows : Vertex (k+h+1)→Fin B)
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    multiplicity (by omega) C k h hk room S ho false origins z rows v=2^(k+h)-1 := by
  rw [multiplicity_retained]
  exact ZeroUpperIncidence.large_retained_count he C k h hk S ho v


end Geometric

namespace Actual
section Definitions
variable {V : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k) (exceptional : Bool)

noncomputable abbrev orientedSource (epsilon : Bool) (a : Address k) (z : Fin 2) :=
  Geometric.orientedSource he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (ZeroUpperCodeOrigins.data he k hk room exceptional C) epsilon a z

noncomputable abbrev multiplicity (z : Fin 2) (rows : Vertex (k+1)→Fin B)
    (v : VertexPower V k×VertexPower V k) :=
  Geometric.multiplicity he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (ZeroUpperCodeOrigins.data he k hk room exceptional C) z rows v

end Definitions

/-- Genuine zero-upper-depth singleton profiles have physical L-1 baseline
incidence at every vertex, including forced k=2. No origin or balance input. -/
theorem small_multiplicity {V : Type} {B : Nat} (C : ClockData V (2^2)) (t : Nat)
    (room : 2^(t+2+3)∣lengthPower (2^2) (t+2)) (z : Fin 2)
    (rows : Vertex (t+2+1)→Fin B) (v : VertexPower V (t+2)×VertexPower V (t+2)) :
    multiplicity (by omega) C (t+2) (by omega) room true z rows v=2^(t+2)-1 := by
  exact Geometric.small_multiplicity C t 0 (by simpa using room)
    (ZeroUpperCodeOrigins.selectors (t+2) (by omega) room true)
    (ZeroUpperCodeOrigins.odd (t+2) (by omega) room true)
    (ZeroUpperCodeOrigins.data (by omega) (t+2) (by omega) room true C) z rows v

/-- Same literal baseline multiplicity at every larger actual parent. -/
theorem large_multiplicity {V : Type} {e B : Nat} (he : 4≤e) (C : ClockData V (2^e))
    (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k) (z : Fin 2)
    (rows : Vertex (k+1)→Fin B) (v : VertexPower V k×VertexPower V k) :
    multiplicity (by omega) C k hk room false z rows v=2^k-1 := by
  exact Geometric.large_multiplicity he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room false)
    (ZeroUpperCodeOrigins.odd k hk room false)
    (ZeroUpperCodeOrigins.data (by omega) k hk room false C) z rows v
end Actual
#print axioms Actual.small_multiplicity
#print axioms Actual.large_multiplicity
#print axioms small_unique_code_owner
#print axioms large_unique_code_owner

namespace Reciprocal
open SquareLift PairedArc
private theorem exponent_room (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega
private theorem coarse_div {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponent_room (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have hd : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 hd

section Source
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
  (exceptional : Bool)
  (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a)
local notation "K" => 2^(e*2^(k+h+1)-1)
local notation "periodN" => 2^(k+h+1)
local notation "hN" => Nat.mul_pos (Nat.two_pow_pos (e*2^(k+h+1)-1)) (by decide : 0<2)

noncomputable def arc (epsilon : Bool) (a : Address (k+h)) :
    DirectedArc hN (castClock (SourceLengths.fine_length he k h 1 (by omega))
      (SourceProfile.clock he C k h S ho epsilon a)) 2 := by
  let D := origins a
  cases epsilon
  · exact SourceReciprocalExchange.castArc (SourceLengths.fine_length he k h 1 (by omega)) rfl _ hN _ D.arcFalse
  · exact SourceReciprocalExchange.castArc (SourceLengths.fine_length he k h 1 (by omega)) rfl _ hN _ D.arcTrue

theorem arc_start_equal (a : Address (k+h)) :
    (arc he C k h hk S ho exceptional origins false a).vertex ⟨0,by omega⟩=
    (arc he C k h hk S ho exceptional origins true a).vertex ⟨0,by omega⟩ := by
  simp only [arc,SourceReciprocalExchange.castArc_zero]
  exact (origins a).start_equal

theorem arc_end_equal (a : Address (k+h)) :
    (arc he C k h hk S ho exceptional origins false a).vertex ⟨2,by omega⟩=
    (arc he C k h hk S ho exceptional origins true a).vertex ⟨2,by omega⟩ := by
  simp only [arc,SourceReciprocalExchange.castArc_last]
  exact (origins a).end_equal

theorem true_clock (a : Address (k+h)) (z : Fin 2) :
    Geometric.orientedSource he C k h hk room S ho exceptional origins true a z=
      ReciprocalEndpoints.forwardClock hN
        (castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho true a))
        (arc he C k h hk S ho exceptional origins true a)
        (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [Geometric.orientedSource,ReciprocalEndpoints.forwardClock,
    OrientedClock.index,Bool.not_true,Bool.false_eq_true,ite_false,MersenneCodeOrigins.endpoint,
    ite_true,arc,SourceReciprocalExchange.castArc_last,SourceReciprocalExchange.castClock_position_eq,
    SourceReciprocalExchange.threshold_eq]

theorem false_clock (a : Address (k+h)) (z : Fin 2) :
    Geometric.orientedSource he C k h hk room S ho exceptional origins false a z=
      ReciprocalEndpoints.reverseClock hN
        (castClock (SourceLengths.fine_length he k h 1 (by omega)) (SourceProfile.clock he C k h S ho false a))
        (arc he C k h hk S ho exceptional origins false a)
        (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [Geometric.orientedSource,ReciprocalEndpoints.reverseClock,
    OrientedClock.index,Bool.not_false,MersenneCodeOrigins.endpoint,Bool.false_eq_true,
    ite_false,ite_true,arc,SourceReciprocalExchange.castArc_zero,SourceReciprocalExchange.castClock_position_eq,
    SourceReciprocalExchange.threshold_eq]

noncomputable def markSet (H : Bool→Address (k+h)→ClockData W B) (post epsilon : Bool)
    (a : Address (k+h)) (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) : Prop :=
  let G := Geometric.orientedSource he C k h hk room S ho exceptional origins epsilon a z
  let hK := Nat.two_pow_pos (e*2^(k+h+1)-1)
  let t := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN))
  AACMarkExchange.ImageSet (ReciprocalEndpoints.host G (H epsilon a))
    (AACMarkIntervals.IsMark hK (if post then AACInduction.turnsAfter hK t (B-1) else fun w=>t w.1) z) v

private theorem long_seams :
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=periodN))
    t ⟨0,Nat.two_pow_pos _⟩=false ∧
    t ⟨1,by have := SourceLengths.coarse_size he k h 1 (by omega); omega⟩=false ∧
    t (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true := by
  have hp : 8≤periodN := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  dsimp only
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.long_zero hp
  constructor
  · unfold TurnPatterns.repeated
    have ht : (⟨1%(2*periodN),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _))⟩ : Fin (2*periodN))=
        ⟨1,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [ht]; exact TurnPatterns.long_one hp
  · have hs : predecessor (Nat.two_pow_pos _) (⟨0,Nat.two_pow_pos _⟩ : Fin K)=⟨K-1,by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega⟩ := by
      apply Fin.ext; simp [predecessor,Nat.mod_eq_of_lt (show K-1<K by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega)]
    rw [hs,TurnPatterns.repeated_last _ (Nat.two_pow_pos _) (coarse_div he k h)]
    exact TurnPatterns.long_last hp

/-- Actual per-address surgery from constructed physical arcs and long
seam values; no exchanged-set or preservation premise. -/
theorem pair_preservation (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (a : Address (k+h))
    (hlast : (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H true true a z v)+
    AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H true false a z v)=
    AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H false true a z v)+
    AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H false false a z v) := by
  dsimp only [markSet]
  rw [true_clock he C k h hk room S ho exceptional origins a z,
    false_clock he C k h hk room S ho exceptional origins a z]
  have hs := long_seams he k h hk
  exact ReciprocalEndpoints.preservation
    (by have := SourceLengths.coarse_size he k h 1 (by omega); omega) (by decide) hB
    _ _ (arc he C k h hk S ho exceptional origins true a)
    (arc he C k h hk S ho exceptional origins false a)
    (arc_start_equal he C k h hk S ho exceptional origins a).symm
    (arc_end_equal he C k h hk S ho exceptional origins a).symm
    (H true a) (H false a) hlast z _ _ hs.1 hs.2.1 hs.2.2 hs.1 hs.2.1 hs.2.2 v

/-- Full numeric configuration postflip incidence equals the actual baseline
family; reserved-slot one enumeration is independently proved complete. -/
theorem postflip_eq_baseline (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (hlast : ∀a, (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk room S ho exceptional origins H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk room S ho exceptional origins H false
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum := by
  apply DenseCodePairs.aggregate_exchange 1 (show 1<k+h+1 by omega)
    (fun eps a=>AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H true eps a z v))
    (fun eps a=>AACMarkExchange.incidence (markSet he C k h hk room S ho exceptional origins H false eps a z v))
  intro a
  have hp := pair_preservation he C k h hk room S ho exceptional origins hB H a (hlast a) z v
  simpa only [Nat.add_comm] using hp

private theorem indicator_sum {X : Type} (l : List X) (P : X→Prop) :
    (l.map (fun x=>if P x then 1 else 0)).sum=l.countP (fun x=>decide (P x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases hp : P x <;> simp [hp,ih,Nat.add_comm]

/-- Literal baseline physical images have the actual count supplied by
MersennePhysicalIncidence; even configuration-dependent H rows are allowed. -/
theorem baseline_eq_multiplicity (H : Bool→Address (k+h)→ClockData W B)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk room S ho exceptional origins H false
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    Geometric.multiplicity he C k h hk room S ho exceptional origins z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  simp only [markSet,Bool.false_eq_true,ite_false,AACMarkExchange.incidence,
    SourceMarkMulticover.host_image_iff,Geometric.multiplicity]
  exact indicator_sum _ _

/-- Exact all-configuration postflip count derived from actual baseline and
actual source arc surgery, not a postflip multiplicity input. -/
theorem postflip_eq_multiplicity (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (hlast : ∀a, (H true a).cycle ⟨B-1,by omega⟩=(H false a).cycle ⟨B-1,by omega⟩)
    (z : Fin 2) (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk room S ho exceptional origins H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    Geometric.multiplicity he C k h hk room S ho exceptional origins z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  rw [postflip_eq_baseline he C k h hk room S ho exceptional origins hB H hlast z v]
  exact baseline_eq_multiplicity he C k h hk room S ho exceptional origins H z v

/-- Actual H decomposition data supplies the common physical last vertex
internally, preserving its full Hamilton edge partition. -/
theorem normalized_eq_multiplicity {R : W→W→Prop} {m : Nat} (hB : 0<B)
    (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (k+h)→Fin m) (z : Fin 2)
    (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(k+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet he C k h hk room S ho exceptional origins H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=
    Geometric.multiplicity he C k h hk room S ho exceptional origins z
      (fun q=>(H (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)).position v.2) v.1 := by
  dsimp only
  apply postflip_eq_multiplicity he C k h hk room S ho exceptional origins hB _ _ z v
  intro a
  exact (HamiltonCommonLast.last_vertex HD last (assigned true a)).trans
    (HamiltonCommonLast.last_vertex HD last (assigned false a)).symm

end Source
end Reciprocal

namespace Actual
section Definitions
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k) (exceptional : Bool)

noncomputable abbrev markSet (H : Bool→Address k→ClockData W B) (post epsilon : Bool)
    (a : Address k) (z : Fin 2) (v : (VertexPower V k×VertexPower V k)×W) :=
  Reciprocal.markSet he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (ZeroUpperCodeOrigins.data he k hk room exceptional C) H post epsilon a z v

end Definitions

/-- Actual normalized H factors give the zero-depth postflip physical count.
Address-dependent singleton profiles and origins are constructed internally. -/
theorem normalized_small {V W : Type} {B m : Nat} {R : W→W→Prop}
    (C : ClockData V (2^2)) (t : Nat)
    (room : 2^(t+2+3)∣lengthPower (2^2) (t+2))
    (hB : 0<B) (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (t+2)→Fin m) (z : Fin 2)
    (v : (VertexPower V (t+2)×VertexPower V (t+2))×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(t+2+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (by omega) C (t+2) (by omega) room true H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=2^(t+2)-1 := by
  dsimp only
  exact (Reciprocal.normalized_eq_multiplicity (by omega) C (t+2) 0 (by omega)
    (by simpa using room) (ZeroUpperCodeOrigins.selectors (t+2) (by omega) room true)
    (ZeroUpperCodeOrigins.odd (t+2) (by omega) room true) true
    (ZeroUpperCodeOrigins.data (by omega) (t+2) (by omega) room true C)
    hB HD last assigned z v).trans (small_multiplicity C t room z _ v.1)

/-- Same exact zero-depth postflip count at all larger parents. -/
theorem normalized_large {V W : Type} {e B m : Nat} {R : W→W→Prop}
    (he : 4≤e) (C : ClockData V (2^e)) (k : Nat) (hk : 2≤k)
    (room : 2^(k+3)∣lengthPower (2^e) k)
    (hB : 0<B) (HD : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address k→Fin m) (z : Fin 2)
    (v : (VertexPower V k×VertexPower V k)×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(k+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (by omega) C k hk room false H true
        (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q) z v))).sum=2^k-1 := by
  dsimp only
  exact (Reciprocal.normalized_eq_multiplicity (by omega) C k 0 hk
    (by simpa using room) (ZeroUpperCodeOrigins.selectors k hk room false)
    (ZeroUpperCodeOrigins.odd k hk room false) false
    (ZeroUpperCodeOrigins.data (by omega) k hk room false C)
    hB HD last assigned z v).trans (large_multiplicity he C k hk room z _ v.1)
end Actual
#print axioms Actual.normalized_small
#print axioms Actual.normalized_large
#print axioms Reciprocal.pair_preservation
end ErdePaths.ZeroUpperIncidence
