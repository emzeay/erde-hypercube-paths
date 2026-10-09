import ErdePaths.SquareLift
import ErdePaths.HierarchicalDecode

namespace ErdePaths.SourceClock
open SquareLift

/-- Actual inverse coordinates of a spanning simple parent cycle. Graph
adjacency is orthogonal to this position-clock calculation. -/
structure ClockData (V : Type) (N : Nat) where
  cycle : Fin N → V
  position : V → Fin N
  position_cycle : ∀ i, position (cycle i)=i
  cycle_position : ∀ v, cycle (position v)=v

/-- Lexicographic macro position: N vertices in each source column. -/
def pairIndex {N : Nat} (a : Fin N × Fin N) : Fin (N*N) :=
  ⟨N*a.1.val+a.2.val,by
    have hm := Nat.mul_le_mul_left N (show a.1.val+1≤N by omega)
    rw [Nat.mul_add,Nat.mul_one] at hm
    have := a.2.isLt
    omega⟩

def pairCoordinates {N : Nat} (hN : 0<N) (t : Fin (N*N)) : Fin N × Fin N :=
  (⟨t.val/N,by
    exact Nat.div_lt_of_lt_mul t.isLt⟩,⟨t.val%N,Nat.mod_lt _ hN⟩)

theorem pairCoordinates_index {N : Nat} (hN : 0<N) (a : Fin N × Fin N) :
    pairCoordinates hN (pairIndex a)=a := by
  apply Prod.ext <;> apply Fin.ext
  · simp only [pairCoordinates,pairIndex]
    rw [Nat.mul_add_div hN,Nat.div_eq_of_lt a.2.isLt,Nat.add_zero]
  · simp only [pairCoordinates,pairIndex,Nat.mul_add_mod,Nat.mod_eq_of_lt a.2.isLt]

theorem pairIndex_coordinates {N : Nat} (hN : 0<N) (t : Fin (N*N)) :
    pairIndex (pairCoordinates hN t)=t := by
  apply Fin.ext
  exact Nat.div_add_mod t.val N

/-- Minus macros run through source columns in reverse order. -/
def negate {N : Nat} (hN : 0<N) (i : Fin N) : Fin N := backward hN ⟨0,hN⟩ i

theorem negate_involutive {N : Nat} (hN : 0<N) (i : Fin N) : negate hN (negate hN i)=i :=
  backward_inverse hN ⟨0,hN⟩ i

def plusPosition {N : Nat} (a : Fin N × Fin N) : Fin (N*N) := pairIndex a

def minusPosition {N : Nat} (hN : 0<N) (a : Fin N × Fin N) : Fin (N*N) :=
  pairIndex (negate hN a.1,a.2)

/-- Actual physical inverse clock of the checked plusVertex construction. -/
def plusClock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (v : V×V) : Fin (N*N) :=
  plusPosition (C.position v.1,backward hN (C.position v.1) (C.position v.2))

def minusClock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (v : V×V) : Fin (N*N) :=
  minusPosition hN (C.position v.2,backward hN (C.position v.1) (C.position v.2))

def plusTour {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (t : Fin (N*N)) : V×V :=
  plusVertex hN C.cycle (pairCoordinates hN t)

def minusTour {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (t : Fin (N*N)) : V×V :=
  let a := pairCoordinates hN t
  minusVertex hN C.cycle (negate hN a.1,a.2)

theorem plusClock_vertex {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (a : Fin N × Fin N) :
    plusClock hN C (plusVertex hN C.cycle a)=plusPosition a := by
  simp only [plusClock,plusVertex,C.position_cycle,backward_inverse]

theorem minusClock_vertex {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (a : Fin N × Fin N) :
    minusClock hN C (minusVertex hN C.cycle a)=minusPosition hN a := by
  simp only [minusClock,minusVertex,C.position_cycle]
  have hh := forward_inverse hN a.1 (forward hN a.1 a.2)
  have hr : backward hN (forward hN a.1 a.2) a.1=a.2 :=
    forward_injective hN a.1 hh
  rw [hr]

theorem plusTour_clock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (v : V×V) :
    plusTour hN C (plusClock hN C v)=v := by
  simp only [plusTour,plusClock,plusPosition,pairCoordinates_index,plusVertex,
    C.cycle_position,backward_inverse]

theorem plusClock_tour {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (t : Fin (N*N)) :
    plusClock hN C (plusTour hN C t)=t := by
  rw [plusTour,plusClock_vertex]
  exact pairIndex_coordinates hN t

theorem minusTour_clock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (v : V×V) :
    minusTour hN C (minusClock hN C v)=v := by
  simp only [minusTour,minusClock,minusPosition,pairCoordinates_index,negate_involutive,minusVertex]
  rw [forward_inverse,C.cycle_position,C.cycle_position]

theorem minusClock_tour {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (t : Fin (N*N)) :
    minusClock hN C (minusTour hN C t)=t := by
  simp only [minusTour,minusClock_vertex,minusPosition,negate_involutive]
  exact pairIndex_coordinates hN t

/-- Divisibility removes the macro-column contribution in the actual clock. -/
theorem pairIndex_mod {N D : Nat} (hD : D∣N) (a : Fin N × Fin N) :
    (pairIndex a).val%D=a.2.val%D := by
  simp only [pairIndex,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hD,Nat.zero_mul,
    Nat.zero_mod,Nat.zero_add,Nat.mod_mod]

theorem plusClock_mod {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N) (C : ClockData V N) (v : V×V) :
    (plusClock hN C v).val%D=
      (N-(C.position v.2).val+(C.position v.1).val)%D := by
  rw [plusClock,plusPosition,pairIndex_mod hD]
  exact Nat.mod_mod_of_dvd _ hD

theorem minusClock_mod {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N) (C : ClockData V N) (v : V×V) :
    (minusClock hN C v).val%D=
      (N-(C.position v.2).val+(C.position v.1).val)%D := by
  rw [minusClock,minusPosition,pairIndex_mod hD]
  exact Nat.mod_mod_of_dvd _ hD

theorem siblings_common_clock {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N) (C : ClockData V N) (v : V×V) :
    (plusClock hN C v).val%D=(minusClock hN C v).val%D :=
  (plusClock_mod hN hD C v).trans (minusClock_mod hN hD C v).symm

/-- The checked position bijections, packaged for repeated actual squares. -/
def squareClock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) : Bool → ClockData (V×V) (N*N)
  | false => ⟨plusTour hN C,plusClock hN C,plusClock_tour hN C,plusTour_clock hN C⟩
  | true => ⟨minusTour hN C,minusClock hN C,minusClock_tour hN C,minusTour_clock hN C⟩

theorem squareClock_mod {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N)
    (C : ClockData V N) (b : Bool) (v : V×V) :
    ((squareClock hN C b).position v).val%D=
      (N-(C.position v.2).val+(C.position v.1).val)%D := by
  cases b
  · exact plusClock_mod hN hD C v
  · exact minusClock_mod hN hD C v

/-- Integer subtraction prevents a hidden truncated-subtraction assumption.
The natural N−j is valid because actual parent positions satisfy j<N. -/
theorem difference_residue_congr {N D i j i' j' : Nat}
    (hj : j<N) (hj' : j'<N) (hi : i%D=i'%D) (hv : j%D=j'%D) :
    (N-j+i)%D=(N-j'+i')%D := by
  apply Int.natCast_inj.mp
  have hc : ((N-j+i : Nat) : Int)=(N : Int)-(j : Int)+(i : Int) := by omega
  have hc' : ((N-j'+i' : Nat) : Int)=(N : Int)-(j' : Int)+(i' : Int) := by omega
  have hi' : (i : Int)%(D : Int)=(i' : Int)%(D : Int) := by
    rw [←Int.natCast_emod,←Int.natCast_emod,hi]
  have hv' : (j : Int)%(D : Int)=(j' : Int)%(D : Int) := by
    rw [←Int.natCast_emod,←Int.natCast_emod,hv]
  rw [Int.natCast_emod,Int.natCast_emod,hc,hc']
  calc
    ((N : Int)-(j : Int)+(i : Int))%(D : Int) =
      (((N : Int)%(D : Int)-(j : Int)%(D : Int))%(D : Int)+(i : Int)%(D : Int))%(D : Int) := by
        rw [Int.add_emod,Int.sub_emod]
    _ = (((N : Int)%(D : Int)-(j' : Int)%(D : Int))%(D : Int)+(i' : Int)%(D : Int))%(D : Int) := by
        rw [hi',hv']
    _ = ((N : Int)-(j' : Int)+(i' : Int))%(D : Int) := by
        symm
        rw [Int.add_emod,Int.sub_emod]

/-- One actual diagonal square preserves any common parent clock modulus,
independently of both child branch choices. -/
theorem common_clock_square {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N)
    (C C' : ClockData V N)
    (hclock : ∀ v, (C.position v).val%D=(C'.position v).val%D)
    (b b' : Bool) (v : V×V) :
    ((squareClock hN C b).position v).val%D=((squareClock hN C' b').position v).val%D := by
  rw [squareClock_mod hN hD,squareClock_mod hN hD]
  exact difference_residue_congr (C.position v.2).isLt (C'.position v.2).isLt
    (hclock v.1) (hclock v.2)

def VertexPower (V : Type) : Nat → Type
  | 0 => V
  | k+1 => VertexPower V k × VertexPower V k

def lengthPower (N : Nat) : Nat → Nat
  | 0 => N
  | k+1 => lengthPower N k * lengthPower N k

theorem lengthPower_positive {N : Nat} (hN : 0<N) (k : Nat) : 0<lengthPower N k := by
  induction k with
  | zero => exact hN
  | succ k ih => exact Nat.mul_pos ih ih

theorem lengthPower_divisible {N D : Nat} (hD : D∣N) (k : Nat) : D∣lengthPower N k := by
  induction k with
  | zero => exact hD
  | succ k ih => exact Nat.dvd_trans ih (Nat.dvd_mul_right (lengthPower N k) (lengthPower N k))

/-- A genuine nested-coordinate source hierarchy, indexed by actual Boolean
branch addresses. Lower address coordinates choose earlier squares. -/
def iteratedClock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) :
    (k : Nat) → (Fin k → Bool) → ClockData (VertexPower V k) (lengthPower N k)
  | 0,_ => C
  | k+1,address => squareClock (lengthPower_positive hN k)
      (iteratedClock hN C k (fun i => address i.castSucc)) (address (Fin.last k))

/-- Entire later subtrees preserve a known common reduced parent clock.
No common full position clock between different source factors is assumed. -/
theorem descendants_common_clock {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N)
    (C C' : ClockData V N)
    (hclock : ∀ v, (C.position v).val%D=(C'.position v).val%D)
    (k : Nat) (address address' : Fin k → Bool) (v : VertexPower V k) :
    ((iteratedClock hN C k address).position v).val%D=
      ((iteratedClock hN C' k address').position v).val%D := by
  induction k with
  | zero => exact hclock v
  | succ k ih =>
    exact common_clock_square (lengthPower_positive hN k) (lengthPower_divisible hD k)
      (iteratedClock hN C k (fun i => address i.castSucc))
      (iteratedClock hN C' k (fun i => address' i.castSucc))
      (fun u => ih (fun i => address i.castSucc) (fun i => address' i.castSucc) u)
      (address (Fin.last k)) (address' (Fin.last k)) v

theorem lengthPower_dvd_later (N j k : Nat) (hjk : j≤k) : lengthPower N j∣lengthPower N k := by
  induction k generalizing j with
  | zero =>
    have hj : j=0 := by omega
    subst j
    exact Nat.dvd_refl _
  | succ k ih =>
    by_cases hj : j≤k
    · exact Nat.dvd_trans (ih j hj) (Nat.dvd_mul_right (lengthPower N k) (lengthPower N k))
    · have he : j=k+1 := by omega
      subst j
      exact Nat.dvd_refl _

/-- Explicit prefix causality for the actual recursive diagonal source
clocks: once a lower branch prefix is fixed, every later branch is invisible
modulo a divisor of that prefix's parent length. -/
theorem source_prefix_common_clock {V : Type} {N D : Nat} (hN : 0<N)
    (C : ClockData V N) (k j : Nat) (hjk : j≤k) (hD : D∣lengthPower N j)
    (address address' : Fin k → Bool)
    (hp : HierarchicalDecode.AgreeBelow j address address') (v : VertexPower V k) :
    ((iteratedClock hN C k address).position v).val%D=
      ((iteratedClock hN C k address').position v).val%D := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    by_cases hj : j≤k
    · have hDk := Nat.dvd_trans hD (lengthPower_dvd_later N j k hj)
      apply common_clock_square (lengthPower_positive hN k) hDk
      intro u
      apply ih j hj hD
      intro i hi
      exact hp i.castSucc hi
    · have hje : j=k+1 := by omega
      have he : address=address' := by
        funext i
        exact hp i (by rw [hje]; exact i.isLt)
      rw [he]

/-- Both siblings and all their suffixes have the same reduced physical
clock, at any branch whose parent length is divisible by the modulus. -/
theorem sibling_subtrees_common_clock {V : Type} {N D : Nat} (hN : 0<N) (hD : D∣N)
    (C : ClockData V N) (b b' : Bool) (k : Nat)
    (address address' : Fin k → Bool) (v : VertexPower (V×V) k) :
    ((iteratedClock (Nat.mul_pos hN hN) (squareClock hN C b) k address).position v).val%D=
      ((iteratedClock (Nat.mul_pos hN hN) (squareClock hN C b') k address').position v).val%D := by
  apply descendants_common_clock (Nat.mul_pos hN hN)
    (Nat.dvd_trans hD (Nat.dvd_mul_right N N))
  intro u
  exact common_clock_square hN hD C C (fun _ => rfl) b b' u

/-- Even parent length alone supplies every low-bit modulus required by
strict-prefix decoding at successive actual diagonal branches. -/
theorem branch_bit_modulus {N : Nat} (hEven : 2∣N) (j : Nat) :
    2^(j+1)∣lengthPower N j := by
  induction j with
  | zero => simpa only [lengthPower,Nat.zero_add,Nat.pow_one] using hEven
  | succ j ih =>
    change 2^((j+1)+1)∣lengthPower N j*lengthPower N j
    rw [Nat.pow_succ]
    exact Nat.mul_dvd_mul ih (lengthPower_divisible hEven j)

/-- Actual low source-clock bits at a physical nested product vertex. -/
def sourceBits {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (k : Nat) (v : VertexPower V k) : HierarchicalDecode.Address k → HierarchicalDecode.Address k :=
  fun address i => ((iteratedClock hN C k address).position v).val.testBit i.val

/-- Strict causality is proved from actual diagonal clock formulas and
parent-length divisibility; it is not assumed for the source family. -/
theorem sourceBits_strictlyCausal {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (k : Nat) (v : VertexPower V k) :
    HierarchicalDecode.StrictlyCausal (sourceBits hN C k v) := by
  intro i address address' hp
  have hm := source_prefix_common_clock hN C k i.val (Nat.le_of_lt i.isLt)
    (branch_bit_modulus hEven i.val) address address' hp v
  have hb := congrArg (fun n : Nat => n.testBit i.val) hm
  simpa only [Nat.testBit_mod_two_pow,show (decide (i.val<i.val+1))=true from by simp,
    Bool.true_and,sourceBits] using hb

/-- Constructive unique actual source owner for an unshifted low-clock
address class. The conclusion is derived, not an input ownership premise. -/
theorem unique_source_address {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (k : Nat) (v : VertexPower V k) :
    ∃ address : HierarchicalDecode.Address k,
      address=sourceBits hN C k v address ∧
      ∀ address', address'=sourceBits hN C k v address' → address'=address := by
  let F := sourceBits hN C k v
  have hc := sourceBits_strictlyCausal hN hEven C k v
  let target : HierarchicalDecode.Address k := fun _ => false
  let address := HierarchicalDecode.decode F target
  have hcorrect := HierarchicalDecode.decode_correct F hc target
  have hfixed : address=F address := by
    funext i
    have he := congrFun hcorrect i
    change (address i ^^ F address i)=false at he
    exact Bool.xor_left_inj.mp (he.trans (Bool.xor_self (F address i)).symm)
  refine ⟨address,hfixed,?_⟩
  intro address' hfixed'
  apply (HierarchicalDecode.unique_solution F hc target).2 address'
  funext i
  change (address' i ^^ F address' i)=false
  rw [congrFun hfixed' i,Bool.xor_self]

/-- Genuine cyclic subtraction by a fixed arbitrary shift, using a positive
period and its residue so Nat subtraction is never silently truncated. -/
def shiftedResidue (M δ x : Nat) : Nat := (x+(M-δ%M))%M

theorem shiftedResidue_subtraction {M : Nat} (hM : 0<M) (δ x : Nat) :
    ((shiftedResidue M δ x : Nat) : Int)=((x : Int)-(δ : Int))%(M : Int) := by
  have hδ := Nat.mod_lt δ hM
  have hc : ((x+(M-δ%M) : Nat) : Int)=(x : Int)+(M : Int)-(δ%M : Nat) := by omega
  rw [shiftedResidue,Int.natCast_emod,hc,Int.natCast_emod,Int.sub_emod_emod]
  have hs : (x : Int)+(M : Int)-(δ : Int)=((x : Int)-(δ : Int))+(M : Int) := by omega
  rw [hs,Int.add_emod_right]

def shiftedSourceBits {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (k : Nat) (v : VertexPower V k) (δ : Nat) :
    HierarchicalDecode.Address k → HierarchicalDecode.Address k :=
  fun address i => (shiftedResidue (2^k) δ
    ((iteratedClock hN C k address).position v).val).testBit i.val

/-- Modular subtraction, including every borrow, preserves causality of the
actual source-clock low bits. The shift may be any natural number. -/
theorem shiftedSourceBits_strictlyCausal {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (k : Nat) (v : VertexPower V k) (δ : Nat) :
    HierarchicalDecode.StrictlyCausal (shiftedSourceBits hN C k v δ) := by
  intro i address address' hp
  have hm := source_prefix_common_clock hN C k i.val (Nat.le_of_lt i.isLt)
    (branch_bit_modulus hEven i.val) address address' hp v
  have hs := Nat.add_mod_eq_add_mod_right (2^k-δ%(2^k)) hm
  have hb := congrArg (fun n : Nat => n.testBit i.val) hs
  have hi1 : decide (i.val<i.val+1)=true := by simp
  have hik : decide (i.val<k)=true := by simp [i.isLt]
  simpa only [shiftedSourceBits,shiftedResidue,Nat.testBit_mod_two_pow,hi1,hik,Bool.true_and] using hb

/-- Unique actual address class after a fixed arithmetic clock shift. -/
theorem unique_shifted_source_address {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (k : Nat) (v : VertexPower V k) (δ : Nat) :
    ∃ address : HierarchicalDecode.Address k,
      address=shiftedSourceBits hN C k v δ address ∧
      ∀ address', address'=shiftedSourceBits hN C k v δ address' → address'=address := by
  let F := shiftedSourceBits hN C k v δ
  have hc := shiftedSourceBits_strictlyCausal hN hEven C k v δ
  let target : HierarchicalDecode.Address k := fun _ => false
  let address := HierarchicalDecode.decode F target
  have hcorrect := HierarchicalDecode.decode_correct F hc target
  have hfixed : address=F address := by
    funext i
    have he := congrFun hcorrect i
    change (address i ^^ F address i)=false at he
    exact Bool.xor_left_inj.mp (he.trans (Bool.xor_self (F address i)).symm)
  refine ⟨address,hfixed,?_⟩
  intro address' hfixed'
  apply (HierarchicalDecode.unique_solution F hc target).2 address'
  funext i
  change (address' i ^^ F address' i)=false
  rw [congrFun hfixed' i,Bool.xor_self]

/-- Fixed arithmetic shifts congruent in a smaller modulus have identical
shifted residues in that modulus, including all cyclic borrows. -/
theorem shiftedResidue_congr {M D : Nat} (hM : 0<M) (hD : D∣M)
    (δ δ' x : Nat) (hδ : δ%D=δ'%D) :
    shiftedResidue M δ x%D=shiftedResidue M δ' x%D := by
  have hd : (δ%M)%D=(δ'%M)%D := by
    rw [Nat.mod_mod_of_dvd _ hD,Nat.mod_mod_of_dvd _ hD,hδ]
  have hc := difference_residue_congr (Nat.mod_lt δ hM) (Nat.mod_lt δ' hM)
    (show 0%D=0%D from rfl) hd
  simp only [Nat.add_zero] at hc
  simp only [shiftedResidue,Nat.mod_mod_of_dvd _ hD]
  exact Nat.add_mod_eq_add_mod_left x hc

theorem shiftedSourceBits_prefix_congr {V : Type} {N : Nat} (hN : 0<N)
    (C : ClockData V N) (k a : Nat) (ha : a≤k) (v : VertexPower V k)
    (δ δ' : Nat) (hδ : δ%(2^a)=δ'%(2^a)) (address : HierarchicalDecode.Address k) :
    HierarchicalDecode.AgreeBelow a (shiftedSourceBits hN C k v δ address)
      (shiftedSourceBits hN C k v δ' address) := by
  intro i hi
  have hm := shiftedResidue_congr (Nat.two_pow_pos k) (Nat.pow_dvd_pow 2 ha) δ δ'
    ((iteratedClock hN C k address).position v).val hδ
  have hb := congrArg (fun n : Nat => n.testBit i.val) hm
  simpa only [Nat.testBit_mod_two_pow,show decide (i.val<a)=true from by simp [hi],
    Bool.true_and,shiftedSourceBits] using hb

/-- The actual shifted owners have the same lower source address whenever
their full arithmetic shifts agree in that lower modulus. -/
theorem shifted_owner_prefix_stability {V : Type} {N : Nat} (hN : 0<N) (hEven : 2∣N)
    (C : ClockData V N) (k a : Nat) (ha : a≤k) (v : VertexPower V k)
    (δ δ' : Nat) (hδ : δ%(2^a)=δ'%(2^a))
    (address address' : HierarchicalDecode.Address k)
    (hx : address=shiftedSourceBits hN C k v δ address)
    (hy : address'=shiftedSourceBits hN C k v δ' address') :
    HierarchicalDecode.AgreeBelow a address address' := by
  apply HierarchicalDecode.reflects_prefix (shiftedSourceBits hN C k v δ)
    (shiftedSourceBits_strictlyCausal hN hEven C k v δ) a address address'
  intro i hi
  have hsame := shiftedSourceBits_prefix_congr hN C k a ha v δ δ' hδ address' i hi
  change (address i ^^ shiftedSourceBits hN C k v δ address i)=
    (address' i ^^ shiftedSourceBits hN C k v δ address' i)
  rw [congrFun hx i,hsame,congrFun hy i,Bool.xor_self,Bool.xor_self]

#print axioms shifted_owner_prefix_stability
#print axioms shiftedResidue_subtraction
#print axioms shiftedSourceBits_strictlyCausal
#print axioms unique_shifted_source_address
#print axioms sourceBits_strictlyCausal
#print axioms unique_source_address
#print axioms source_prefix_common_clock
#print axioms sibling_subtrees_common_clock
#print axioms common_clock_square
#print axioms descendants_common_clock
#print axioms siblings_common_clock
#print axioms plusClock_tour
#print axioms minusClock_tour
end ErdePaths.SourceClock
