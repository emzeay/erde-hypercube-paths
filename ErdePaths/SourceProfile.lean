import ErdePaths.HamiltonProfile
import ErdePaths.MarkSchedule

namespace ErdePaths.SourceProfile
open SourceClock Profile HierarchicalDecode

def castClock {V : Type} {M N : Nat} (h : M=N) (C : ClockData V M) : ClockData V N := by
  subst N; exact C

theorem castClock_position {V : Type} {M N : Nat} (h : M=N) (C : ClockData V M) (v : V) :
    ((castClock h C).position v).val=(C.position v).val := by subst N; rfl

theorem lengthPower_pow (e a : Nat) : lengthPower (2^e) a=2^(e*2^a) := by
  induction a with
  | zero => simp [lengthPower]
  | succ a ih =>
    simp only [lengthPower,ih,Nat.pow_succ]
    rw [←Nat.pow_add]
    congr 1
    rw [←Nat.mul_assoc,Nat.mul_two]

theorem exponent_bound {e : Nat} (he : 2≤e) (a : Nat) : a+2≤e*2^a := by
  induction a with
  | zero => simpa using he
  | succ a ih =>
    rw [Nat.pow_succ,←Nat.mul_assoc,Nat.mul_two]
    omega

/-- Actual prefix-square parent, reindexed by its proved power-of-two length. -/
def prefixClock {V : Type} {e : Nat} (C : ClockData V (2^e)) (a : Nat) (address : Address a) :
    ClockData (VertexPower V a) (2^(e*2^a)) :=
  castClock (lengthPower_pow e a) (iteratedClock (Nat.two_pow_pos e) C a address)

/-- The one genuine positive-profile stage after a standard source prefix. -/
noncomputable def profileClock {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (address : Address a) (epsilon : Bool) :
    ClockData (VertexPower V a × VertexPower V a) ((2^(e*2^a))*(2^(e*2^a))) :=
  ProfileLift.clock (by have := exponent_bound he a; omega)
    (prefixClock C a address) (S address) (ho address) epsilon

def lowerAddress {a h : Nat} (address : Address (a+h)) : Address a :=
  fun i => address ⟨i.val,by have := i.isLt; omega⟩

def upperAddress {a h : Nat} (address : Address (a+h)) : Address h :=
  fun i => address ⟨a+i.val,by have := i.isLt; omega⟩

/-- Source bits omit the profile stage: lower bits precede it and upper bits
follow it. The selector is attached to the actual lower source parent. -/
noncomputable def clock {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool) (address : Address (a+h)) :
    ClockData (VertexPower (VertexPower V a × VertexPower V a) h)
      (lengthPower ((2^(e*2^a))*(2^(e*2^a))) h) :=
  iteratedClock (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (profileClock he C a S ho (lowerAddress address) epsilon) h (upperAddress address)

/-- Actual lower-parent residues survive any fresh selector, profile twin,
and every later square. No reduced-clock equality is assumed. -/
theorem lower_prefix_common {V : Type} {e D : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h j : Nat) (hja : j≤a) (hd : D∣lengthPower (2^e) j)
    (S T : Address a → Fin (2^(e*2^a)) → Bool)
    (hs : ∀ address, cardinality (S address)%2=1)
    (ht : ∀ address, cardinality (T address)%2=1)
    (epsilon epsilon' : Bool) (address address' : Address (a+h))
    (hp : AgreeBelow j address address')
    (v : VertexPower (VertexPower V a × VertexPower V a) h) :
    ((clock he C a h S hs epsilon address).position v).val%D=
      ((clock he C a h T ht epsilon' address').position v).val%D := by
  have hda : D∣2^(e*2^a) := by
    rw [←lengthPower_pow]
    exact Nat.dvd_trans hd (lengthPower_dvd_later (2^e) j a hja)
  apply descendants_common_clock (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (Nat.dvd_trans hda (Nat.dvd_mul_right _ _))
  intro u
  apply ProfileLift.common_clock (by have := exponent_bound he a; omega) hda
  intro w
  simp only [prefixClock,castClock_position]
  apply source_prefix_common_clock (Nat.two_pow_pos e) C a j hja hd
  intro i hi
  exact hp ⟨i.val,by have := i.isLt; omega⟩ hi

/-- Upper source causality comes from identical actual profile parents once
their lower addresses agree, then from the checked later-square formulas. -/
theorem upper_prefix_common {V : Type} {e D : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h j : Nat) (haj : a≤j) (hj : j≤a+h)
    (hd : D∣lengthPower ((2^(e*2^a))*(2^(e*2^a))) (j-a))
    (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (epsilon : Bool) (address address' : Address (a+h))
    (hp : AgreeBelow j address address')
    (v : VertexPower (VertexPower V a × VertexPower V a) h) :
    ((clock he C a h S ho epsilon address).position v).val%D=
      ((clock he C a h S ho epsilon address').position v).val%D := by
  have hl : lowerAddress address=lowerAddress address' := by
    funext i
    exact hp ⟨i.val,by have := i.isLt; omega⟩ (by change i.val<j; have := i.isLt; omega)
  unfold clock
  rw [hl]
  apply source_prefix_common_clock _ _ h (j-a) (by omega) hd
  intro i hi
  exact hp ⟨a+i.val,by have := i.isLt; omega⟩ (by change a+i.val<j; omega)

/-- Strengthened parent-length divisibility accounts for the reserved bit. -/
theorem offset_bit_modulus {N c : Nat} (hc : 2^c∣N) (heven : 2∣N) (q : Nat) :
    2^(c+q)∣lengthPower N q := by
  induction q with
  | zero => simpa [lengthPower] using hc
  | succ q ih =>
    change 2^(c+(q+1))∣lengthPower N q*lengthPower N q
    rw [show c+(q+1)=c+q+1 by omega,Nat.pow_succ]
    exact Nat.mul_dvd_mul ih (lengthPower_divisible heven q)

def sparsePosition (a j : Nat) : Nat := if j<a then j else j+1

theorem strong_bit_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (i : Fin (a+h)) (address address' : Address (a+h))
    (hp : AgreeBelow i.val address address')
    (v : VertexPower (VertexPower V a × VertexPower V a) h) :
    ((clock he C a h S ho epsilon address).position v).val%(2^(i.val+2))=
      ((clock he C a h S ho epsilon address').position v).val%(2^(i.val+2)) := by
  by_cases hi : i.val<a
  · have heven : 2∣2^e := by simpa using Nat.pow_dvd_pow 2 (show 1≤e by omega)
    have hfour : 2^2∣2^e := Nat.pow_dvd_pow 2 he
    simpa only [Nat.add_comm] using lower_prefix_common he C a h i.val (by omega) (offset_bit_modulus hfour heven i.val)
      S S ho ho epsilon epsilon address address' hp v
  · have hpbase : 2^(a+2)∣(2^(e*2^a))*(2^(e*2^a)) := by
      rw [←Nat.pow_add]
      apply Nat.pow_dvd_pow
      have := exponent_bound he a
      omega
    have heven : 2∣(2^(e*2^a))*(2^(e*2^a)) := by
      apply Nat.dvd_trans (show 2∣2^(a+2) by simpa using Nat.pow_dvd_pow 2 (show 1≤a+2 by omega)) hpbase
    have hd := offset_bit_modulus hpbase heven (i.val-a)
    have hex : a+2+(i.val-a)=i.val+2 := by omega
    rw [hex] at hd
    exact upper_prefix_common he C a h i.val (by omega) (by have := i.isLt; omega) hd
      S ho epsilon address address' hp v

/-- Reserved CODE position r is independent of the physical profile depth a. -/
theorem sparse_bit_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (i : Fin (a+h)) (address address' : Address (a+h))
    (hp : AgreeBelow i.val address address')
    (v : VertexPower (VertexPower V a × VertexPower V a) h) :
    ((clock he C a h S ho epsilon address).position v).val%(2^(sparsePosition r i.val+1))=
      ((clock he C a h S ho epsilon address').position v).val%(2^(sparsePosition r i.val+1)) := by
  have hm := strong_bit_common he C a h S ho epsilon i address address' hp v
  have hd : 2^(sparsePosition r i.val+1)∣2^(i.val+2) := by
    apply Nat.pow_dvd_pow
    unfold sparsePosition; split <;> omega
  have hh := congrArg (fun n => n%(2^(sparsePosition r i.val+1))) hm
  simpa only [Nat.mod_mod_of_dvd _ hd] using hh

theorem sparsePosition_lt (r K : Nat) (i : Fin K) : sparsePosition r i.val<K+1 := by
  unfold sparsePosition; split <;> have := i.isLt <;> omega

/-- Actual arithmetic subtraction, including borrows across the reserved bit. -/
noncomputable def shiftedBits {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat) :
    Address (a+h) → Address (a+h) := fun address i =>
  (shiftedResidue (2^(a+h+1)) delta
    ((clock he C a h S ho epsilon address).position v).val).testBit (sparsePosition r i.val)

/-- Sparse causality is derived from actual clocks with reservation r
independent of the physical prefix/profile stage a. -/
theorem shiftedBits_strictlyCausal {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat) :
    StrictlyCausal (shiftedBits he C a h r S ho epsilon v delta) := by
  intro i address address' hp
  have hm := sparse_bit_common he C a h r S ho epsilon i address address' hp v
  have hs := Nat.add_mod_eq_add_mod_right (2^(a+h+1)-delta%(2^(a+h+1))) hm
  have hb := congrArg (fun n => n.testBit (sparsePosition r i.val)) hs
  have hi1 : decide (sparsePosition r i.val<sparsePosition r i.val+1)=true := by simp
  have hit : decide (sparsePosition r i.val<a+h+1)=true := by
    exact decide_eq_true (sparsePosition_lt r (a+h) i)
  simpa only [shiftedBits,shiftedResidue,Nat.testBit_mod_two_pow,hi1,hit,Bool.true_and] using hb

/-- Unconditional unique source owner for every physical vertex and arithmetic
shift, with the profile twin fixed and the reserved code bit arbitrary. -/
theorem unique_shifted_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat) :
    ∃ address : Address (a+h), address=shiftedBits he C a h r S ho epsilon v delta address ∧
      ∀ address', address'=shiftedBits he C a h r S ho epsilon v delta address' → address'=address := by
  let F := shiftedBits he C a h r S ho epsilon v delta
  have hc := shiftedBits_strictlyCausal he C a h r S ho epsilon v delta
  let target : Address (a+h) := fun _ => false
  let address := HierarchicalDecode.decode F target
  have hcorrect := HierarchicalDecode.decode_correct F hc target
  have hfixed : address=F address := by
    funext i
    have hh := congrFun hcorrect i
    change (address i ^^ F address i)=false at hh
    exact Bool.xor_left_inj.mp (hh.trans (Bool.xor_self (F address i)).symm)
  refine ⟨address,hfixed,?_⟩
  intro address' hf
  apply (HierarchicalDecode.unique_solution F hc target).2 address'
  funext i
  change (address' i ^^ F address' i)=false
  rw [congrFun hf i,Bool.xor_self]

noncomputable def shiftedValue {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat)
    (address : Address (a+h)) : Nat :=
  shiftedResidue (2^(a+h+1)) delta ((clock he C a h S ho epsilon address).position v).val

/-- Actual code room makes the complete shifted value independent of the
profile twin, at every source address, including all upper choices. -/
theorem shiftedValue_twin_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (epsilon epsilon' : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat)
    (address : Address (a+h)) :
    shiftedValue he C a h S ho epsilon v delta address =
      shiftedValue he C a h S ho epsilon' v delta address := by
  have hm := lower_prefix_common he C a h a (Nat.le_refl _) room S S ho ho
    epsilon epsilon' address address (fun _ _ => rfl) v
  exact Nat.add_mod_eq_add_mod_right (2^(a+h+1)-delta%(2^(a+h+1))) hm

/-- Joint source/profile ownership follows from actual clock room. Reserved
code bit r and physical profile depth a are independent parameters. -/
theorem unique_joint_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (_hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat) :
    ∃ epsilon address,
      address=shiftedBits he C a h r S ho epsilon v delta address ∧
      epsilon=(shiftedValue he C a h S ho epsilon v delta address).testBit r ∧
      ∀ epsilon' address',
        address'=shiftedBits he C a h r S ho epsilon' v delta address' →
        epsilon'=(shiftedValue he C a h S ho epsilon' v delta address').testBit r →
        epsilon'=epsilon ∧ address'=address := by
  obtain ⟨address,hfixed,hunique⟩ := unique_shifted_owner he C a h r S ho false v delta
  let epsilon := (shiftedValue he C a h S ho false v delta address).testBit r
  have hf (b : Bool) (addr : Address (a+h)) :
      shiftedBits he C a h r S ho b v delta addr =
        shiftedBits he C a h r S ho false v delta addr := by
    funext i
    exact congrArg (fun n => n.testBit (sparsePosition r i.val))
      (shiftedValue_twin_common he C a h S ho room b false v delta addr)
  refine ⟨epsilon,address,?_,?_,?_⟩
  · rw [hf]; exact hfixed
  · exact (congrArg (fun n => n.testBit r)
      (shiftedValue_twin_common he C a h S ho room epsilon false v delta address)).symm
  · intro b addr hsrc hprof
    rw [hf] at hsrc
    have ha := hunique addr hsrc
    refine ⟨?_,ha⟩
    subst addr
    rw [shiftedValue_twin_common he C a h S ho room b false v delta address] at hprof
    exact hprof

/-- The paper's numeric room inequality supplies the exact divisibility used
by joint ownership, with no clock or causality premise. -/
theorem code_room {e a h : Nat} (room : a+h+1≤e*2^a) :
    2^(a+h+1)∣lengthPower (2^e) a := by
  rw [lengthPower_pow]
  exact Nat.pow_dvd_pow 2 room

#print axioms unique_joint_owner
#print axioms unique_shifted_owner
#print axioms shiftedBits_strictlyCausal
#print axioms sparse_bit_common
#print axioms lower_prefix_common
end ErdePaths.SourceProfile
