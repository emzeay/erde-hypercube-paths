import ErdePaths.CubeHierarchy
import ErdePaths.CubeParity

set_option backward.isDefEq.respectTransparency false

namespace ErdePaths.SourceParity
open SourceClock SourceProfile SourceFactors CubeHierarchy SquareLift HamiltonData HamiltonTower Profile

/-- Both literal standard tours start at the same doubled parent origin. -/
theorem square_zero {V N} (hN : 0<N) (C : ClockData V N) (b : Bool) :
    (squareClock hN C b).cycle ⟨0,Nat.mul_pos hN hN⟩=(C.cycle ⟨0,hN⟩,C.cycle ⟨0,hN⟩) := by
  have hb : backward hN (⟨0,hN⟩ : Fin N) ⟨0,hN⟩=⟨0,hN⟩ := by
    apply Fin.ext
    simp [backward]
  cases b
  · simp only [squareClock,plusTour,pairCoordinates,plusVertex,Nat.zero_div,Nat.zero_mod,hb]
  · simp only [squareClock,minusTour,pairCoordinates,minusVertex,negate,Nat.zero_div,Nat.zero_mod,hb]
    have hf : forward hN (⟨0,hN⟩ : Fin N) ⟨0,hN⟩=⟨0,hN⟩ := by apply Fin.ext; simp [forward]
    rw [hf]

/-- Every odd profile/twin has literal numeric origin (0,0). -/
theorem profile_zero {V : Type} {e : Nat} (he : 1≤e) (C : ClockData V (2^e))
    (S : Fin (2^e)→Bool) (ho : cardinality S%2=1) (b : Bool) :
    (ProfileLift.clock he C S ho b).cycle ⟨0,Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)⟩=
      (C.cycle ⟨0,Nat.two_pow_pos e⟩,C.cycle ⟨0,Nat.two_pow_pos e⟩) := by
  have hb : backward (Nat.two_pow_pos e) (⟨0,Nat.two_pow_pos e⟩ : Fin (2^e))
      ⟨0,Nat.two_pow_pos e⟩=⟨0,Nat.two_pow_pos e⟩ := by apply Fin.ext; simp [backward]
  simp only [ProfileLift.clock,ProfileLift.map,profileClockData,profileCycles,profileTour,
    pairCoordinates,profileVertex,Nat.zero_div,Nat.zero_mod,Nat.zero_mul,prefixCount,Nat.zero_add,hb]

/-- A literal squared origin has even physical parity, without any assumption
on the parent origin or arbitrary vertex coloring. -/
theorem tower_origin_even {V R n N} (I : Coordinates V R n) (hN : 0<N)
    (C : ClockData V N) (k : Nat) (address : HierarchicalDecode.Address (k+1)) :
    CubeParity.parity ((tower I (k+1)).encode
      ((iteratedClock hN C (k+1) address).cycle ⟨0,lengthPower_positive hN (k+1)⟩))=false := by
  have hz : CubeParity.parity ((product (tower I k)).encode
      ((squareClock (lengthPower_positive hN k)
        (iteratedClock hN C k (fun i => address i.castSucc)) (address (Fin.last k))).cycle
        ⟨0,Nat.mul_pos (lengthPower_positive hN k) (lengthPower_positive hN k)⟩))=false := by
    rw [square_zero]
    exact (CubeParity.product_parity _).trans (Bool.xor_self _)
  simpa only [iteratedClock,tower,VertexPower,lengthPower] using hz

theorem cast_parity {V R n d} (eqn : n=d) (I : Coordinates V R n) (v : V) :
    CubeParity.parity ((castCoordinates eqn I).encode v)=CubeParity.parity (I.encode v) := by
  subst d; rfl

/-- All actual source/profile origins are even after actual cube encoding;
the genuine fresh profile already enforces this at zero upper depth. -/
theorem source_origin_even {n e : Nat} (he : 2≤e) (C : ClockData (Vertex n) (2^e))
    (k h : Nat) (S : HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ a, cardinality (S a)%2=1) (epsilon : Bool) (address : HierarchicalDecode.Address (k+h)) :
    CubeParity.parity ((sourceIso n k h).encode
      ((clock he C k h S ho epsilon address).cycle
        ⟨0,lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h⟩))=false := by
  unfold sourceIso
  rw [cast_parity]
  cases h with
  | zero =>
    have hz : CubeParity.parity ((product (tower (identity n) k)).encode
      ((profileClock he C k S ho (lowerAddress address) epsilon).cycle
        ⟨0,Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)⟩))=false := by
      change CubeParity.parity ((product (tower (identity n) k)).encode
        ((ProfileLift.clock _ (prefixClock C k (lowerAddress address)) _ _ epsilon).cycle _))=false
      rw [profile_zero]
      exact (CubeParity.product_parity _).trans (Bool.xor_self _)
    simpa only [clock,iteratedClock,sourceCoordinates,tower,VertexPower,lengthPower] using hz
  | succ h =>
    exact tower_origin_even (product (tower (identity n) k)) _ _ h _

/-- The constructed actual cube factor has even literal origin. -/
theorem cube_origin_even {n m e : Nat}
    (D : DecompositionData (Vertex n) (@Adjacent n) m (2^e) (Nat.two_pow_pos e))
    (he : 2≤e) (k h : Nat)
    (S : Fin m → HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f a, cardinality (S f a)%2=1)
    (f : Fin m) (epsilon : Bool) (address : HierarchicalDecode.Address (k+h)) :
    CubeParity.parity (((cubeFamily D he k h S ho).cycles (index k h f epsilon address)).cycle
      ⟨0,lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h⟩)=false := by
  change CubeParity.parity ((sourceIso n k h).encode
    (((family D he k h S ho).cycles (index k h f epsilon address)).cycle _))=false
  have hc := SourceFactors.clock_eq D he k h S ho f epsilon address
  have hh := congrArg (fun C => C.cycle
    ⟨0,lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h⟩) hc
  rw [hh]
  exact source_origin_even he (D.cycles f).toClockData k h (S f) (ho f) epsilon address

/-- Even origin fixes the phase: actual inverse position bit0 is exactly
physical cube parity, not a supplied coloring of the physical vertices. -/
theorem position_parity {n N : Nat} (hN : 0<N)
    (C : CycleData (Vertex n) (@Adjacent n) N hN)
    (horigin : CubeParity.parity (C.cycle ⟨0,hN⟩)=false) (v : Vertex n) :
    (C.position v).val.testBit 0=CubeParity.parity v := by
  have hc := CubeParity.clock_parity hN C (C.position v)
  rw [C.cycle_position,horigin,AACUnfold.flipN_mod] at hc
  rw [Nat.testBit_zero]
  have hm : (C.position v).val%2<2 := Nat.mod_lt _ (by decide)
  by_cases hz : (C.position v).val%2=0
  · simp only [hz,ite_true] at hc
    simp only [hz,show (0 : Nat)≠1 from by decide,decide_false]
    exact hc.symm
  · have hone : (C.position v).val%2=1 := by omega
    simp only [hone,show ¬(1 : Nat)=0 from by decide,ite_false] at hc
    simpa only [hone,decide_true,Bool.not_false] using hc.symm

/-- Literal source/profile clock bit0 equals the parity of its explicit actual
cube encoding. Initial parent origin phase need not be assumed even. -/
theorem source_position_parity {n m e : Nat}
    (D : DecompositionData (Vertex n) (@Adjacent n) m (2^e) (Nat.two_pow_pos e))
    (he : 2≤e) (k h : Nat)
    (S : Fin m → HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f a, cardinality (S f a)%2=1)
    (f : Fin m) (epsilon : Bool) (address : HierarchicalDecode.Address (k+h))
    (v : VertexPower (VertexPower (Vertex n) k × VertexPower (Vertex n) k) h) :
    ((clock he (D.cycles f).toClockData k h (S f) (ho f) epsilon address).position v).val.testBit 0=
      CubeParity.parity ((sourceIso n k h).encode v) := by
  have hp := position_parity _ ((cubeFamily D he k h S ho).cycles (index k h f epsilon address))
    (cube_origin_even D he k h S ho f epsilon address) ((sourceIso n k h).encode v)
  rw [cube_position,(sourceIso n k h).decode_encode] at hp
  exact hp

/-- Even cyclic offsets preserve the actual parity bit, including subtraction
borrows and reduction in any even positive cyclic modulus. -/
theorem even_shift_bit {M : Nat} (hm : 0<M) (hM : 2∣M) (delta x : Nat)
    (hd : delta%2=0) : (shiftedResidue M delta x).testBit 0=x.testBit 0 := by
  have hs := shiftedResidue_congr hm hM delta 0 x (by simpa using hd)
  have hz : shiftedResidue M 0 x%2=x%2 := by
    simp only [shiftedResidue,Nat.zero_mod,Nat.sub_zero]
    rw [Nat.mod_mod_of_dvd _ hM,Nat.add_mod,Nat.mod_eq_zero_of_dvd hM,Nat.add_zero,Nat.mod_mod]
  have hh := hs.trans hz
  simp only [Nat.testBit_zero,hh]

/-- Shifted literal clocks retain physical parity for any proved even offset;
this is the parity input to the exceptional Mersenne correction. -/
theorem shifted_source_parity {n m e M : Nat}
    (D : DecompositionData (Vertex n) (@Adjacent n) m (2^e) (Nat.two_pow_pos e))
    (he : 2≤e) (k h : Nat)
    (S : Fin m → HierarchicalDecode.Address k → Fin (2^(e*2^k)) → Bool)
    (ho : ∀ f a, cardinality (S f a)%2=1)
    (f : Fin m) (epsilon : Bool) (address : HierarchicalDecode.Address (k+h))
    (v : VertexPower (VertexPower (Vertex n) k × VertexPower (Vertex n) k) h)
    (hm : 0<M) (hM : 2∣M) (delta : Nat) (hd : delta%2=0) :
    (shiftedResidue M delta
      ((clock he (D.cycles f).toClockData k h (S f) (ho f) epsilon address).position v).val).testBit 0=
      CubeParity.parity ((sourceIso n k h).encode v) := by
  rw [even_shift_bit hm hM delta _ hd]
  exact source_position_parity D he k h S ho f epsilon address v

#print axioms shifted_source_parity
#print axioms source_position_parity
#print axioms square_zero
#print axioms profile_zero
#print axioms source_origin_even
end ErdePaths.SourceParity
