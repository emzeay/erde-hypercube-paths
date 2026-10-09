import Std

namespace ErdePaths.HierarchicalDecode

abbrev Address (r : Nat) := Fin r → Bool

/-- Agreement on the strict prefix of length a. Bounds exceeding r are
allowed; no index outside Fin r is introduced. -/
def AgreeBelow {r : Nat} (a : Nat) (x y : Address r) : Prop :=
  ∀ i : Fin r, i.val<a → x i=y i

/-- Coordinate i of the clock is independent of the address at i and later. -/
def StrictlyCausal {r : Nat} (F : Address r → Address r) : Prop :=
  ∀ (i : Fin r) (x y : Address r), AgreeBelow i.val x y → F x i=F y i

def addressXor {r : Nat} (F : Address r → Address r) (x : Address r) : Address r :=
  fun i => x i ^^ F x i

/-- Explicit forward substitution: solve bit n while retaining earlier bits.
No choice, finite search, or assumed inverse occurs in this definition. -/
def stage {r : Nat} (F : Address r → Address r) (target : Address r) : Nat → Address r
  | 0 => fun _ => false
  | n+1 => fun i => if i.val=n then target i ^^ F (stage F target n) i else stage F target n i

theorem stage_preserves_prefix {r : Nat} (F : Address r → Address r)
    (target : Address r) (n : Nat) : AgreeBelow n (stage F target (n+1)) (stage F target n) := by
  intro i hi
  simp only [stage,ite_eq_right (show i.val≠n by omega)]

private theorem xor_twice (x y : Bool) : ((x ^^ y) ^^ y)=x := by
  rw [Bool.xor_assoc,Bool.xor_self,Bool.xor_false]

/-- Each finite stage has correctly solved every earlier output bit. -/
theorem stage_solves_prefix {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (target : Address r) (n : Nat) :
    AgreeBelow n (addressXor F (stage F target n)) target := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hclock : F (stage F target (n+1)) i=F (stage F target n) i := by
      apply hF i
      intro j hj
      exact stage_preserves_prefix F target n j (by omega)
    by_cases hin : i.val<n
    · change (stage F target (n+1) i ^^ F (stage F target (n+1)) i)=target i
      rw [stage_preserves_prefix F target n i hin,hclock]
      exact ih i hin
    · have hei : i.val=n := by omega
      change (stage F target (n+1) i ^^ F (stage F target (n+1)) i)=target i
      rw [hclock]
      simp only [stage,ite_eq_left hei]
      exact xor_twice _ _

def decode {r : Nat} (F : Address r → Address r) (target : Address r) : Address r := stage F target r

theorem decode_correct {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (target : Address r) : addressXor F (decode F target)=target := by
  funext i
  exact stage_solves_prefix F hF target r i i.isLt

/-- The triangular transformation reflects prefix agreement. This is stronger
than injectivity and supplies hierarchical profile-bit stability. -/
theorem reflects_prefix {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (a : Nat) (x y : Address r)
    (hxy : AgreeBelow a (addressXor F x) (addressXor F y)) : AgreeBelow a x y := by
  have aux : ∀ n, n≤a → AgreeBelow n x y := by
    intro n
    induction n with
    | zero => intro _ i hi; omega
    | succ n ih =>
      intro hn i hi
      by_cases hin : i.val<n
      · exact ih (by omega) i hin
      · have hei : i.val=n := by omega
        have hp : AgreeBelow i.val x y := by
          rw [hei]
          exact ih (by omega)
        have hc := hF i x y hp
        have he := hxy i (by omega)
        change (x i ^^ F x i)=(y i ^^ F y i) at he
        rw [hc] at he
        exact Bool.xor_left_inj.mp he
  exact aux a (Nat.le_refl a)

/-- Prefix causality also means the transformation preserves each prefix. -/
theorem preserves_prefix {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (a : Nat) (x y : Address r)
    (hxy : AgreeBelow a x y) : AgreeBelow a (addressXor F x) (addressXor F y) := by
  intro i hi
  have hc := hF i x y (fun j hj => hxy j (by omega))
  simp only [addressXor,hxy i hi,hc]

theorem prefix_equivalence {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (a : Nat) (x y : Address r) :
    AgreeBelow a (addressXor F x) (addressXor F y) ↔ AgreeBelow a x y :=
  ⟨reflects_prefix F hF a x y,preserves_prefix F hF a x y⟩

theorem addressXor_injective {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) : Function.Injective (addressXor F) := by
  intro x y he
  have hp : AgreeBelow r (addressXor F x) (addressXor F y) := by
    intro i _
    exact congrFun he i
  have hs := reflects_prefix F hF r x y hp
  funext i
  exact hs i i.isLt

theorem addressXor_surjective {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) : Function.Surjective (addressXor F) :=
  fun target => ⟨decode F target,decode_correct F hF target⟩

theorem addressXor_bijective {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) : Function.Injective (addressXor F) ∧ Function.Surjective (addressXor F) :=
  ⟨addressXor_injective F hF,addressXor_surjective F hF⟩

/-- Every arbitrarily shifted target has precisely its constructed solution. -/
theorem unique_solution {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (target : Address r) :
    addressXor F (decode F target)=target ∧
      ∀ x, addressXor F x=target → x=decode F target :=
  ⟨decode_correct F hF target,fun _ hx => addressXor_injective F hF (hx.trans (decode_correct F hF target).symm)⟩

/-- Arbitrary solutions with targets agreeing below a have equal address
prefixes, even if the targets differ at all later coordinates. -/
theorem solutions_prefix {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (a : Nat) (target target' x y : Address r)
    (hx : addressXor F x=target) (hy : addressXor F y=target')
    (ht : AgreeBelow a target target') : AgreeBelow a x y := by
  apply reflects_prefix F hF a x y
  simpa only [hx,hy] using ht

theorem decode_prefix {r : Nat} (F : Address r → Address r)
    (hF : StrictlyCausal F) (a : Nat) (target target' : Address r)
    (ht : AgreeBelow a target target') : AgreeBelow a (decode F target) (decode F target') :=
  solutions_prefix F hF a target target' _ _ (decode_correct F hF target) (decode_correct F hF target') ht

#print axioms decode_correct
#print axioms addressXor_bijective
#print axioms unique_solution
#print axioms solutions_prefix
#print axioms decode_prefix
end ErdePaths.HierarchicalDecode
