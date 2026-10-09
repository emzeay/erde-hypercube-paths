import ErdePaths.ProfileLift

namespace ErdePaths.MersenneClock
open SourceClock SquareLift

/-- The low-clock correction at the first small parent is a law of the
literal diagonal formulas, independent of graph, dimension or odd part. -/
theorem scalar_formula : ∀ a b : Fin 16,
    (minusPosition (by decide : 0<16) (b,backward (by decide) a b)).val%32=
      (17*(plusPosition (a,backward (by decide) a b)).val)%32 := by decide

/-- Physical vertices may be arbitrary: the correction is transported through
actual parent inverse clocks, rather than supplied as a numerical oracle. -/
theorem scalar_clock {V : Type} (C : ClockData V 16) (v : V×V) :
    (minusClock (by decide : 0<16) C v).val%32=
      (17*(plusClock (by decide) C v).val)%32 :=
  scalar_formula (C.position v.1) (C.position v.2)

theorem bit_formula : ∀ a b : Fin 16,
    (minusPosition (by decide : 0<16) (b,backward (by decide) a b)).val.testBit 4=
      ((plusPosition (a,backward (by decide) a b)).val.testBit 4 ^^
        (plusPosition (a,backward (by decide) a b)).val.testBit 0) := by decide

/-- The exceptional source branch changes bit four exactly on odd physical
clock parity. Lower four bits remain common by the ordinary residue theorem. -/
theorem bit_clock {V : Type} (C : ClockData V 16) (v : V×V) :
    (minusClock (by decide : 0<16) C v).val.testBit 4=
      ((plusClock (by decide) C v).val.testBit 4 ^^ (plusClock (by decide) C v).val.testBit 0) :=
  bit_formula (C.position v.1) (C.position v.2)

theorem low_four_clock {V : Type} (C : ClockData V 16) (v : V×V) :
    (minusClock (by decide : 0<16) C v).val%16=
      (plusClock (by decide) C v).val%16 :=
  (siblings_common_clock (by decide) (Nat.dvd_refl 16) C v).symm

/-- Multiplication by seventeen survives the actual DIFF inverse-clock
formula at every larger parent; this is uniform propagation, not a finite test. -/
theorem difference_scalar {N i j i' j' : Nat} (hN : 32∣N)
    (_hi : i<N) (hj : j<N) (_hi' : i'<N) (hj' : j'<N)
    (hx : i'%32=(17*i)%32) (hy : j'%32=(17*j)%32) :
    (N-j'+i')%32=(17*(N-j+i))%32 := by
  have hn := Nat.mod_eq_zero_of_dvd hN
  omega

theorem square_scalar {V : Type} {N : Nat} (hN : 0<N) (hd : 32∣N)
    (C C' : ClockData V N) (hc : ∀v, (C'.position v).val%32=(17*(C.position v).val)%32)
    (b b' : Bool) (v : V×V) :
    ((squareClock hN C' b').position v).val%32=
      (17*((squareClock hN C b).position v).val)%32 := by
  have hnew := squareClock_mod hN hd C' b' v
  have hold := squareClock_mod hN hd C b v
  rw [hnew]
  have hs := difference_scalar hd (C.position v.1).isLt (C.position v.2).isLt
    (C'.position v.1).isLt (C'.position v.2).isLt (hc v.1) (hc v.2)
  rw [hs]
  have hh := congrArg (fun x => (17*x)%32) hold
  simpa only [Nat.mul_mod,Nat.mod_mod] using hh.symm

/-- The fresh profile's SUM formula also preserves the same correction,
independently of arbitrary odd selectors and twin choices. -/
theorem profile_scalar {V : Type} {e : Nat} (he : 1≤e) (hd : 32∣2^e)
    (C C' : ClockData V (2^e))
    (hc : ∀v, (C'.position v).val%32=(17*(C.position v).val)%32)
    (S T : Fin (2^e)→Bool) (hs : Profile.cardinality S%2=1) (ht : Profile.cardinality T%2=1)
    (b b' : Bool) (v : V×V) :
    ((ProfileLift.clock he C' T ht b').position v).val%32=
      (17*((ProfileLift.clock he C S hs b).position v).val)%32 := by
  rw [ProfileLift.clock_mod he hd]
  have hold := ProfileLift.clock_mod he hd C S hs b v
  have hx := hc v.1
  have hy := hc v.2
  have hh := congrArg (fun x => (17*x)%32) hold
  have hsum : ((C'.position v.1).val+(C'.position v.2).val)%32=
      (17*((C.position v.1).val+(C.position v.2).val))%32 := by
    rw [Nat.add_mod,hx,hy,←Nat.add_mod,←Nat.mul_add]
  rw [hsum]
  simpa only [Nat.mul_mod,Nat.mod_mod] using hh.symm

/-- Every later source subtree preserves the correction, for all suffix
addresses. Actual nested inverse clocks, not formal residue symbols, are used. -/
theorem descendants_scalar {V : Type} {N : Nat} (hN : 0<N) (hd : 32∣N)
    (C C' : ClockData V N) (hc : ∀v, (C'.position v).val%32=(17*(C.position v).val)%32)
    (k : Nat) (address address' : Fin k→Bool) (v : VertexPower V k) :
    ((iteratedClock hN C' k address').position v).val%32=
      (17*((iteratedClock hN C k address).position v).val)%32 := by
  induction k with
  | zero => exact hc v
  | succ k ih =>
    exact square_scalar (lengthPower_positive hN k) (lengthPower_divisible hd k)
      (iteratedClock hN C k (fun i => address i.castSucc))
      (iteratedClock hN C' k (fun i => address' i.castSucc))
      (fun u => ih (fun i => address i.castSucc) (fun i => address' i.castSucc) u)
      (address (Fin.last k)) (address' (Fin.last k)) v

/-- In the small-parent branch the new square already has length 256, so
all arbitrarily many later diagonal stages satisfy the required modulus. -/
theorem scalar_subtrees {V : Type} (C : ClockData V 16) (k : Nat)
    (address address' : Fin k→Bool) (v : VertexPower (V×V) k) :
    ((iteratedClock (by decide : 0<16*16) (squareClock (by decide) C true) k address').position v).val%32=
      (17*((iteratedClock (by decide : 0<16*16) (squareClock (by decide) C false) k address).position v).val)%32 :=
  descendants_scalar (by decide) (by decide) _ _ (scalar_clock C) k address address' v

#print axioms scalar_subtrees
#print axioms square_scalar
#print axioms profile_scalar
#print axioms scalar_clock
#print axioms bit_clock
end ErdePaths.MersenneClock
