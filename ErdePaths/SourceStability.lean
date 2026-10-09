import ErdePaths.SourceProfile

namespace ErdePaths.SourceStability
open SourceClock SourceProfile HierarchicalDecode Profile

/-- Modular arithmetic shifts preserve a shared actual reduced clock, including
all subtraction borrows. -/
theorem shifted_congr {M D : Nat} (hm : 0<M) (hd : D∣M)
    (delta delta' x y : Nat) (hs : delta%D=delta'%D) (hx : x%D=y%D) :
    shiftedResidue M delta x%D=shiftedResidue M delta' y%D := by
  have hc := Nat.add_mod_eq_add_mod_right (M-delta%M) hx
  have ht : shiftedResidue M delta x%D=shiftedResidue M delta y%D := by
    simpa only [shiftedResidue,Nat.mod_mod_of_dvd _ hd] using hc
  exact ht.trans (shiftedResidue_congr hm hd delta delta' y hs)

theorem twinBits_common {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (epsilon epsilon' : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta : Nat)
    (address : Address (a+h)) :
    shiftedBits he C a h r S ho epsilon v delta address =
      shiftedBits he C a h r S ho epsilon' v delta address := by
  funext i
  exact congrArg (fun n => n.testBit (sparsePosition r i.val))
    (shiftedValue_twin_common he C a h S ho room epsilon epsilon' v delta address)

theorem shiftBits_prefix {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta delta' : Nat)
    (hd : delta%(2^(r+1))=delta'%(2^(r+1))) (address : Address (a+h)) :
    AgreeBelow r (shiftedBits he C a h r S ho epsilon v delta address)
      (shiftedBits he C a h r S ho epsilon v delta' address) := by
  intro i hi
  have hm := shiftedResidue_congr (Nat.two_pow_pos (a+h+1))
    (Nat.pow_dvd_pow 2 (show r+1≤a+h+1 by omega)) delta delta'
    ((clock he C a h S ho epsilon address).position v).val hd
  have hb := congrArg (fun n => n.testBit i.val) hm
  simpa only [shiftedBits,sparsePosition,ite_eq_left hi,Nat.testBit_mod_two_pow,
    show decide (i.val<r+1)=true from by simp [show i.val<r+1 by omega],Bool.true_and] using hb

/-- Decoded source prefixes agree even across profile twins when shifts agree
modulo twice the reserved-bit scale. This is derived from actual constructors. -/
theorem owner_prefix {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta delta' : Nat)
    (hd : delta%(2^(r+1))=delta'%(2^(r+1))) (epsilon epsilon' : Bool)
    (address address' : Address (a+h))
    (hx : address=shiftedBits he C a h r S ho epsilon v delta address)
    (hy : address'=shiftedBits he C a h r S ho epsilon' v delta' address') :
    AgreeBelow r address address' := by
  rw [twinBits_common he C a h r S ho room epsilon false v delta address] at hx
  rw [twinBits_common he C a h r S ho room epsilon' false v delta' address'] at hy
  apply reflects_prefix (shiftedBits he C a h r S ho false v delta)
    (shiftedBits_strictlyCausal he C a h r S ho false v delta) r address address'
  intro i hi
  have hs := shiftBits_prefix he C a h r hr S ho false v delta delta' hd address' i hi
  change (address i ^^ shiftedBits he C a h r S ho false v delta address i)=
    (address' i ^^ shiftedBits he C a h r S ho false v delta address' i)
  rw [congrFun hx i,hs,congrFun hy i,Bool.xor_self,Bool.xor_self]

theorem clock_reserved_congr {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (epsilon epsilon' : Bool)
    (address address' : Address (a+h)) (hp : AgreeBelow r address address')
    (v : VertexPower (VertexPower V a × VertexPower V a) h) :
    ((clock he C a h S ho epsilon address).position v).val%(2^(r+1))=
      ((clock he C a h S ho epsilon' address').position v).val%(2^(r+1)) := by
  by_cases hra : r≤a
  · have heven : 2∣2^e := by simpa using Nat.pow_dvd_pow 2 (show 1≤e by omega)
    exact lower_prefix_common he C a h r hra (branch_bit_modulus heven r)
      S S ho ho epsilon epsilon' address address' hp v
  · have hd : 2^(r+1)∣lengthPower (2^e) a :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (show r+1≤a+h+1 by omega)) room
    apply lower_prefix_common he C a h a (Nat.le_refl _) hd S S ho ho
      epsilon epsilon' address address' _ v
    intro i hi
    exact hp i (by omega)

/-- Both the lower source prefix and the decoded profile twin are stable under
actual congruent arithmetic shifts. -/
theorem joint_owner_stable {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (delta delta' : Nat)
    (hd : delta%(2^(r+1))=delta'%(2^(r+1))) (epsilon epsilon' : Bool)
    (address address' : Address (a+h))
    (hx : address=shiftedBits he C a h r S ho epsilon v delta address)
    (hy : address'=shiftedBits he C a h r S ho epsilon' v delta' address')
    (hxp : epsilon=(shiftedValue he C a h S ho epsilon v delta address).testBit r)
    (hyp : epsilon'=(shiftedValue he C a h S ho epsilon' v delta' address').testBit r) :
    AgreeBelow r address address' ∧ epsilon=epsilon' := by
  have hp := owner_prefix he C a h r hr S ho room v delta delta' hd epsilon epsilon' address address' hx hy
  have hc := clock_reserved_congr he C a h r hr S ho room epsilon epsilon' address address' hp v
  have hs := shifted_congr (Nat.two_pow_pos (a+h+1))
    (Nat.pow_dvd_pow 2 (show r+1≤a+h+1 by omega)) delta delta' _ _ hd hc
  have hb := congrArg (fun n => n.testBit r) hs
  have hb' : (shiftedValue he C a h S ho epsilon v delta address).testBit r=
      (shiftedValue he C a h S ho epsilon' v delta' address').testBit r := by
    simpa only [shiftedValue,Nat.testBit_mod_two_pow,
      show decide (r<r+1)=true from by simp,Bool.true_and] using hb
  exact ⟨hp,hxp.trans (hb'.trans hyp.symm)⟩

/-- A genuinely owner-dependent offset still has exactly one owner when its
value depends only on the stable profile bit/lower prefix and all offset
values share the required arithmetic residue. No bijection is assumed. -/
theorem unique_variable_offset_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a)
    (v : VertexPower (VertexPower V a × VertexPower V a) h)
    (offset : Bool → Address (a+h) → Nat) (delta0 : Nat)
    (uniform : ∀ b addr, offset b addr%(2^(r+1))=delta0%(2^(r+1)))
    (depends : ∀ b addr addr', AgreeBelow r addr addr' → offset b addr=offset b addr') :
    ∃ epsilon address,
      address=shiftedBits he C a h r S ho epsilon v (offset epsilon address) address ∧
      epsilon=(shiftedValue he C a h S ho epsilon v (offset epsilon address) address).testBit r ∧
      ∀ b addr,
        addr=shiftedBits he C a h r S ho b v (offset b addr) addr →
        b=(shiftedValue he C a h S ho b v (offset b addr) addr).testBit r →
        b=epsilon ∧ addr=address := by
  obtain ⟨b0,x0,hx0,hb0,_⟩ := unique_joint_owner he C a h r hr S ho room v delta0
  let delta := offset b0 x0
  obtain ⟨b,x,hx,hb,hu⟩ := unique_joint_owner he C a h r hr S ho room v delta
  have hd0 : delta0%(2^(r+1))=delta%(2^(r+1)) := (uniform b0 x0).symm
  obtain ⟨hp0,he0⟩ := joint_owner_stable he C a h r hr S ho room v delta0 delta hd0 b0 b x0 x hx0 hx hb0 hb
  have hvalue : delta=offset b x := by
    change offset b0 x0=offset b x
    rw [←he0]
    exact depends b0 x0 x hp0
  refine ⟨b,x,?_,?_,?_⟩
  · simpa only [hvalue] using hx
  · simpa only [hvalue] using hb
  · intro b' x' hx' hb'
    have hd : delta%(2^(r+1))=offset b' x'%(2^(r+1)) :=
      (uniform b0 x0).trans (uniform b' x').symm
    obtain ⟨hp,heb⟩ := joint_owner_stable he C a h r hr S ho room v delta (offset b' x') hd b b' x x' hx hx' hb hb'
    have hoff : delta=offset b' x' := by
      rw [hvalue,←heb]
      exact depends b x x' hp
    rw [←hoff] at hx' hb'
    exact hu b' x' hx' hb'

/-- Nonnegative representatives of the literal offsets +A*u and -A*u. -/
def signedOffset (M A u : Nat) (negative : Bool) : Nat :=
  if negative then shiftedResidue M (A*u) 0 else (A*u)%M

/-- The two oriented offsets have the same residue modulo 2A, retaining the
actual cyclic modulus M rather than truncated natural subtraction. -/
theorem signedOffset_residue {M A : Nat} (hm : 0<M) (ha : 0<A) (hd : 2*A∣M)
    (u : Nat) (negative : Bool) : signedOffset M A u negative%(2*A)=(A*u)%(2*A) := by
  cases negative
  · exact Nat.mod_mod_of_dvd _ hd
  · let z := (A*u)%M
    have hz : z<M := Nat.mod_lt _ hm
    have hd0 : M%(2*A)=0 := Nat.mod_eq_zero_of_dvd hd
    have hr : z%(2*A)=A*(u%2) := by
      rw [Nat.mod_mod_of_dvd _ hd]
      simpa only [Nat.mul_comm 2 A] using Nat.mul_mod_mul_left A u 2
    have hu : u%2<2 := Nat.mod_lt _ (by omega)
    simp only [signedOffset, shiftedResidue, Nat.zero_add, ↓reduceIte]
    change ((M-z)%M)%(2*A)=(A*u)%(2*A)
    rw [Nat.mod_mod_of_dvd _ hd]
    have ht : (A*u)%(2*A)=z%(2*A) := (Nat.mod_mod_of_dvd _ hd).symm
    rw [ht]
    by_cases hzero : u%2=0
    · simp only [hzero,Nat.mul_zero] at hr
      rw [hr]
      exact Nat.sub_mod_eq_zero_of_mod_eq (hd0.trans hr.symm)
    · have hone : u%2=1 := by omega
      simp only [hone,Nat.mul_one] at hr
      have hmod : ((M-z)+A)%(2*A)=0 := by
        have he := congrArg (fun n => n%(2*A)) (Nat.sub_add_cancel (Nat.le_of_lt hz))
        rw [Nat.add_mod,hr,hd0] at he
        rw [Nat.add_mod,Nat.mod_eq_of_lt (show A<2*A by omega)]
        exact he
      have hres := (Nat.mod_eq_sub_iff ha (show A≤2*A by omega)).mpr (Nat.dvd_of_mod_eq_zero hmod)
      rw [hr]
      simpa only [show 2*A-A=A by omega] using hres

/-- Orientation-dependent offsets now have actual unique self-consistent
owners; orientation may read only the proved stable lower prefix/profile bit. -/
theorem unique_oriented_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (room : 2^(a+h+1)∣lengthPower (2^e) a)
    (v : VertexPower (VertexPower V a × VertexPower V a) h) (u : Nat)
    (direction : Bool → Address (a+h) → Bool)
    (depends : ∀ b addr addr', AgreeBelow r addr addr' → direction b addr=direction b addr') :
    ∃ epsilon address,
      address=shiftedBits he C a h r S ho epsilon v
        (signedOffset (2^(a+h+1)) (2^r) u (direction epsilon address)) address ∧
      epsilon=(shiftedValue he C a h S ho epsilon v
        (signedOffset (2^(a+h+1)) (2^r) u (direction epsilon address)) address).testBit r ∧
      ∀ b addr,
        addr=shiftedBits he C a h r S ho b v
          (signedOffset (2^(a+h+1)) (2^r) u (direction b addr)) addr →
        b=(shiftedValue he C a h S ho b v
          (signedOffset (2^(a+h+1)) (2^r) u (direction b addr)) addr).testBit r →
        b=epsilon ∧ addr=address := by
  apply unique_variable_offset_owner he C a h r hr S ho room v
    (fun b addr => signedOffset (2^(a+h+1)) (2^r) u (direction b addr)) ((2^r)*u)
  · intro b addr
    have hd : 2*(2^r)∣2^(a+h+1) := by
      rw [Nat.mul_comm 2,←Nat.pow_succ]
      exact Nat.pow_dvd_pow 2 (by omega)
    have hh := signedOffset_residue (Nat.two_pow_pos (a+h+1)) (Nat.two_pow_pos r) hd u (direction b addr)
    simpa only [Nat.mul_comm 2,←Nat.pow_succ] using hh
  · intro b addr addr' hp
    rw [depends b addr addr' hp]

#print axioms unique_oriented_owner
#print axioms unique_variable_offset_owner
#print axioms joint_owner_stable
end ErdePaths.SourceStability
