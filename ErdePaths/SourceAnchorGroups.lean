import ErdePaths.DenseSourceMarks

namespace ErdePaths.SourceAnchorGroups
open SourceProfile SourceClock HierarchicalDecode

/-- The fixed high address defining one old-anchor group. -/
def InGroup {K : Nat} (r : Nat) (high address : Address K) : Prop :=
  ∀i, r≤i.val→address i=high i

/-- Solve only the low coordinates and force all remaining coordinates. -/
def truncate {K : Nat} (F : Address K→Address K) (r : Nat) (high : Address K) :
    Address K→Address K := fun address i=>if i.val<r then F address i else high i

theorem truncate_causal {K : Nat} (F : Address K→Address K) (hc : StrictlyCausal F)
    (r : Nat) (high : Address K) : StrictlyCausal (truncate F r high) := by
  intro i x y hp
  unfold truncate
  split
  · exact hc i x y hp
  · rfl

theorem truncate_fixed_iff {K : Nat} (F : Address K→Address K) (r : Nat)
    (high address : Address K) : address=truncate F r high address ↔
      InGroup r high address ∧ AgreeBelow r address (F address) := by
  constructor
  · intro he
    constructor
    · intro i hi
      have hh := congrFun he i
      simpa only [truncate,ite_eq_right (show ¬i.val<r by omega)] using hh
    · intro i hi
      have hh := congrFun he i
      simpa only [truncate,ite_eq_left hi] using hh
  · rintro ⟨hg,hl⟩
    funext i
    unfold truncate
    split
    · exact hl i ‹i.val<r›
    · exact hg i (by omega)

/-- A genuine strictly causal decoder has exactly one low-bit solution in
any fixed-high-bit group. No group coverage premise is used. -/
theorem unique_truncated_owner {K : Nat} (F : Address K→Address K) (hc : StrictlyCausal F)
    (r : Nat) (high : Address K) :
    ∃address, InGroup r high address ∧ AgreeBelow r address (F address) ∧
      ∀address', InGroup r high address'→AgreeBelow r address' (F address')→address'=address := by
  let T := truncate F r high
  have ht := truncate_causal F hc r high
  let target : Address K := fun _=>false
  let address := HierarchicalDecode.decode T target
  have hcorrect := HierarchicalDecode.decode_correct T ht target
  have hfixed : address=T address := by
    funext i
    have hh := congrFun hcorrect i
    change (address i ^^ T address i)=false at hh
    exact Bool.xor_left_inj.mp (hh.trans (Bool.xor_self (T address i)).symm)
  have hgroup := (truncate_fixed_iff F r high address).mp hfixed
  refine ⟨address,hgroup.1,hgroup.2,?_⟩
  intro address' hg hl
  have hf := (truncate_fixed_iff F r high address').mpr ⟨hg,hl⟩
  apply (HierarchicalDecode.unique_solution T ht target).2 address'
  funext i
  change (address' i ^^ T address' i)=false
  rw [congrFun hf i,Bool.xor_self]

/-- Actual old-anchor residue ownership, with an arbitrary arithmetic shift.
The profile twin is fixed; high source bits determine the group. -/
noncomputable def Owns {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r≤a+h) (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a×VertexPower V a) h) (delta : Nat)
    (address : Address (a+h)) : Prop :=
  shiftedValue he C a h S ho epsilon v delta address%(2^r)=
    (DenseSourceMarks.code r (by omega) epsilon address).val%(2^r)

/-- Numeric low-r-bit residue equality is exactly the truncated actual
source-clock bit decoder, including all arithmetic subtraction borrows. -/
theorem owns_iff {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r≤a+h) (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1) (epsilon : Bool)
    (v : VertexPower (VertexPower V a×VertexPower V a) h) (delta : Nat)
    (address : Address (a+h)) :
    Owns he C a h r hr S ho epsilon v delta address ↔
    AgreeBelow r address (shiftedBits he C a h r S ho epsilon v delta address) := by
  let value := shiftedValue he C a h S ho epsilon v delta address
  let code := DenseSourceMarks.code r (show r<a+h+1 by omega) epsilon address
  have hb (i : Fin (a+h)) (hi : i.val<r) :
      value.testBit i.val=(shiftedBits he C a h r S ho epsilon v delta address) i := by
    simp only [value,shiftedValue,shiftedBits,sparsePosition,ite_eq_left hi]
  have hc (i : Fin (a+h)) (hi : i.val<r) : code.val.testBit i.val=address i := by
    have hh := DenseSourceMarks.code_source r (show r<a+h+1 by omega) epsilon address i
    simpa only [code,sparsePosition,ite_eq_left hi] using hh
  constructor
  · intro heq i hi
    have hh := congrArg (fun n=>n.testBit i.val) heq
    change (value%(2^r)).testBit i.val=(code.val%(2^r)).testBit i.val at hh
    simp only [Nat.testBit_mod_two_pow,show decide (i.val<r)=true from by simp [hi],Bool.true_and] at hh
    rw [hc i hi,hb i hi] at hh
    exact hh.symm
  · intro hp
    change value%(2^r)=code.val%(2^r)
    suffices hf : (⟨value%(2^r),Nat.mod_lt _ (Nat.two_pow_pos r)⟩ : Vertex r)=
        ⟨code.val%(2^r),Nat.mod_lt _ (Nat.two_pow_pos r)⟩ from congrArg Fin.val hf
    apply binaryTuple_injective (n:=r)
    funext i
    let j : Fin (a+h) := ⟨i.val,by have := i.isLt; omega⟩
    have hi : j.val<r := i.isLt
    have hh := hp j hi
    rw [←hb j hi,←hc j hi] at hh
    simpa only [binaryTuple,Nat.testBit_mod_two_pow,
      show decide (i.val<r)=true from by simp [i.isLt],Bool.true_and] using hh.symm

/-- Unconditional actual unique old-anchor owner inside every fixed-high-bit
group, for every physical vertex, profile twin, and positive/negative shift. -/
theorem unique_group_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r≤a+h) (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1) (epsilon : Bool)
    (high : Address (a+h)) (v : VertexPower (VertexPower V a×VertexPower V a) h) (delta : Nat) :
    ∃address, InGroup r high address ∧ Owns he C a h r hr S ho epsilon v delta address ∧
      ∀address', InGroup r high address'→Owns he C a h r hr S ho epsilon v delta address'→address'=address := by
  obtain ⟨address,hg,hl,hu⟩ := unique_truncated_owner
    (shiftedBits he C a h r S ho epsilon v delta)
    (shiftedBits_strictlyCausal he C a h r S ho epsilon v delta) r high
  refine ⟨address,hg,(owns_iff he C a h r hr S ho epsilon v delta address).mpr hl,?_⟩
  intro address' hg' ho'
  exact hu address' hg' ((owns_iff he C a h r hr S ho epsilon v delta address').mp ho')

/-- Literal low binary tuple insertion; all high source bits stay fixed. -/
def insertLow {K : Nat} (r : Nat) (_hr : r≤K) (high : Address K) (low : Vertex r) : Address K :=
  fun i=>if hi : i.val<r then binaryTuple low ⟨i.val,hi⟩ else high i

theorem insertLow_group {K : Nat} (r : Nat) (hr : r≤K) (high : Address K) (low : Vertex r) :
    InGroup r high (insertLow r hr high low) := by
  intro i hi
  simp only [insertLow,dite_eq_right (show ¬i.val<r by omega)]

theorem insertLow_injective {K : Nat} (r : Nat) (hr : r≤K) (high : Address K) :
    Function.Injective (insertLow r hr high) := by
  intro x y he
  apply binaryTuple_injective
  funext i
  let j : Fin K := ⟨i.val,by have := i.isLt; omega⟩
  have hj : j.val<r := i.isLt
  have hh := congrFun he j
  simpa only [insertLow,dite_eq_left hj] using hh

theorem insertLow_covers {K : Nat} (r : Nat) (hr : r≤K) (high address : Address K)
    (hg : InGroup r high address) : ∃low, insertLow r hr high low=address := by
  let bits : Fin r→Bool := fun i=>address ⟨i.val,by have := i.isLt; omega⟩
  obtain ⟨low,hl⟩ := binaryTuple_surjective bits
  refine ⟨low,?_⟩
  funext i
  unfold insertLow
  split
  · exact congrFun hl ⟨i.val,‹i.val<r›⟩
  · exact (hg i (by omega)).symm

def groupList {K : Nat} (r : Nat) (hr : r≤K) (high : Address K) : List (Address K) :=
  (List.finRange (2^r)).map (insertLow r hr high)

theorem groupList_nodup {K : Nat} (r : Nat) (hr : r≤K) (high : Address K) :
    (groupList r hr high).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.nodup_finRange (2^r)).imp
  intro x y hxy he
  exact hxy (insertLow_injective r hr high he)

theorem groupList_mem_iff {K : Nat} (r : Nat) (hr : r≤K) (high address : Address K) :
    address∈groupList r hr high ↔ InGroup r high address := by
  constructor
  · intro hm
    obtain ⟨low,_,rfl⟩ := List.mem_map.mp hm
    exact insertLow_group r hr high low
  · intro hg
    obtain ⟨low,hl⟩ := insertLow_covers r hr high address hg
    exact List.mem_map.mpr ⟨low,List.mem_finRange low,hl⟩

theorem groupList_length {K : Nat} (r : Nat) (hr : r≤K) (high : Address K) :
    (groupList r hr high).length=2^r := by simp only [groupList,List.length_map,List.length_finRange]

/-- The actual representative partition inside the literal A-factor list. -/
theorem unique_group_list_owner {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r≤a+h) (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1) (epsilon : Bool)
    (high : Address (a+h)) (v : VertexPower (VertexPower V a×VertexPower V a) h) (delta : Nat) :
    ∃address, address∈groupList r hr high ∧ Owns he C a h r hr S ho epsilon v delta address ∧
      ∀address', address'∈groupList r hr high→Owns he C a h r hr S ho epsilon v delta address'→address'=address := by
  obtain ⟨address,hg,ho',hu⟩ := unique_group_owner he C a h r hr S ho epsilon high v delta
  refine ⟨address,(groupList_mem_iff r hr high address).mpr hg,ho',?_⟩
  intro address' hm ho'
  exact hu address' ((groupList_mem_iff r hr high address').mp hm) ho'

/-- Canonical high-address representative from a literal high binary tuple. -/
def highAddress {K : Nat} (r : Nat) (hr : r≤K) (high : Vertex (K-r)) : Address K :=
  fun i=>if hi : r≤i.val then binaryTuple high ⟨i.val-r,by have := i.isLt; omega⟩ else false

theorem highAddress_unique {K : Nat} (r : Nat) (hr : r≤K) (x y : Vertex (K-r))
    (address : Address K) (hx : InGroup r (highAddress r hr x) address)
    (hy : InGroup r (highAddress r hr y) address) : x=y := by
  apply binaryTuple_injective
  funext i
  let j : Fin K := ⟨r+i.val,by have := i.isLt; omega⟩
  have hj : r≤j.val := by change r≤r+i.val; omega
  have he := (hx j hj).symm.trans (hy j hj)
  simpa only [highAddress,dite_eq_left hj,j,Nat.add_sub_cancel_left] using he

theorem highAddress_covers {K : Nat} (r : Nat) (hr : r≤K) (address : Address K) :
    ∃high, InGroup r (highAddress r hr high) address := by
  let bits : Fin (K-r)→Bool := fun i=>address ⟨r+i.val,by have := i.isLt; omega⟩
  obtain ⟨high,he⟩ := binaryTuple_surjective bits
  refine ⟨high,?_⟩
  intro i hi
  have hx := congrFun he ⟨i.val-r,by have := i.isLt; omega⟩
  simpa only [highAddress,dite_eq_left hi,bits,Nat.add_sub_cancel' hi] using hx.symm

/-- Literal group keys: one profile twin and one high binary tuple. -/
def groupKeys (K r : Nat) : List (Bool×Vertex (K-r)) :=
  (List.finRange (2^(K-r))).map (fun q=>(false,q)) ++
  (List.finRange (2^(K-r))).map (fun q=>(true,q))

theorem groupKeys_nodup (K r : Nat) : (groupKeys K r).Nodup := by
  have hn (b : Bool) : ((List.finRange (2^(K-r))).map (fun q=>(b,q))).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange _).imp
    intro x y hxy he
    exact hxy (Prod.mk.inj he).2
  apply List.pairwise_append.mpr
  refine ⟨hn false,hn true,?_⟩
  intro a ha b hb he
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
  have hfalse : false=true := (Prod.mk.inj he).1
  cases hfalse

theorem groupKeys_length (K r : Nat) : (groupKeys K r).length=2*2^(K-r) := by
  simp only [groupKeys,List.length_append,List.length_map,List.length_finRange,Nat.two_mul]

theorem groupKeys_full {K r} (b : Bool) (high : Vertex (K-r)) : (b,high)∈groupKeys K r := by
  cases b <;> simp [groupKeys]

/-- Every source/profile factor belongs to precisely one literal group key. -/
theorem unique_group_key {K : Nat} (r : Nat) (hr : r≤K) (epsilon : Bool) (address : Address K) :
    ∃key : Bool×Vertex (K-r), key∈groupKeys K r ∧ epsilon=key.1 ∧
      InGroup r (highAddress r hr key.2) address ∧
      ∀key', epsilon=key'.1→InGroup r (highAddress r hr key'.2) address→key'=key := by
  obtain ⟨high,hg⟩ := highAddress_covers r hr address
  refine ⟨(epsilon,high),groupKeys_full epsilon high,rfl,hg,?_⟩
  intro key' he hg'
  exact Prod.ext he.symm (highAddress_unique r hr key'.2 high address hg' hg)

/-- Exact number of fixed-twin/high-address groups when high bits are
represented once by their literal binary tuple. -/
theorem number_of_groups (K r : Nat) (hr : r≤K) :
    2*2^(K-r)=2^(K+1-r) := by
  have he : K+1-r=(K-r)+1 := by omega
  rw [he,Nat.pow_succ,Nat.mul_comm]

#print axioms unique_truncated_owner
#print axioms owns_iff
#print axioms unique_group_owner
#print axioms unique_group_list_owner
#print axioms groupList_mem_iff
#print axioms groupList_length
#print axioms unique_group_key
#print axioms groupKeys_nodup
end ErdePaths.SourceAnchorGroups
