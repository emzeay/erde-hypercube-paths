import ErdePaths.HamiltonSquare
import ErdePaths.ProfileLift

namespace ErdePaths.HamiltonProfile
open SquareLift SourceClock HamiltonData Profile HamiltonSquare

/-- The actual product embedding commutes with the exact torus decoder. -/
theorem map_decode {V : Type} {e : Nat} (C : ClockData V (2^e)) (a : TorusEdgeLabel (2^e)) :
    (ProfileLift.map C (decode (Nat.two_pow_pos e) (fun t => t) a).1,
      ProfileLift.map C (decode (Nat.two_pow_pos e) (fun t => t) a).2) =
    decode (Nat.two_pow_pos e) C.cycle a := by
  cases a <;> rfl

/-- Each actual numeric profile edge has its explicit parent-factor torus label. -/
theorem cyclicEdge_decodes {V : Type} {R : V → V → Prop} {m e : Nat}
    (he : 1≤e) (d : DecompositionData V R m (2^e) (Nat.two_pow_pos e))
    (S : Fin m → Fin (2^e) → Bool) (ho : ∀ f, cardinality (S f)%2=1)
    (f : Fin m) (b : Bool) (t : Fin ((2^e)*(2^e))) :
    ((ProfileLift.cycle he (d.cycles f) d.symmetric (S f) (ho f) b).cycle t,
      (ProfileLift.cycle he (d.cycles f) d.symmetric (S f) (ho f) b).cycle
        (successor (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) t)) =
    familyDecode d f (stepLabel (Nat.two_pow_pos e) (S f) b
      (profileCycles (Nat.two_pow_pos e) (S f) b t)) := by
  have hd := map_decode (d.cycles f).toClockData
    (stepLabel (Nat.two_pow_pos e) (S f) b (profileCycles (Nat.two_pow_pos e) (S f) b t))
  rw [step_decodes] at hd
  change (ProfileLift.map (d.cycles f).toClockData (profileCycles (Nat.two_pow_pos e) (S f) b t),
    ProfileLift.map (d.cycles f).toClockData (profileCycles (Nat.two_pow_pos e) (S f) b
      (successor (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) t))) = _
  rw [profileCycles_next]
  exact hd

/-- Arbitrary odd profiles, chosen independently at each parent factor,
produce 2m genuine Hamilton factors and exact global product-edge ownership. -/
noncomputable def profiles {V : Type} {R : V → V → Prop} {m e : Nat}
    (he : 2≤e) (d : DecompositionData V R m (2^e) (Nat.two_pow_pos e))
    (S : Fin m → Fin (2^e) → Bool) (ho : ∀ f, cardinality (S f)%2=1) :
    DecompositionData (V×V) (ProductAdjacent R) (2*m) ((2^e)*(2^e))
      (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) where
  cycles i := ProfileLift.cycle (by omega) (d.cycles (factorCoordinates i).1) d.symmetric
    (S (factorCoordinates i).1) (ho (factorCoordinates i).1) (factorCoordinates i).2
  symmetric := fun _ _ h => productAdjacent_symm d.symmetric h
  loopfree u h := by
    rcases h with h | h
    · exact d.loopfree u.2 h.2
    · exact d.loopfree u.1 h.2
  cover u v huv := by
    obtain ⟨f,a,ha⟩ := familyDecode_cover d u v huv
    obtain ⟨b,x,hx⟩ := labels_cover (Nat.two_pow_pos e) (S f) a
    obtain ⟨t,ht⟩ := profileCycles_surjective (by omega) (S f) (ho f) b x
    refine ⟨factorIndex (f,b),t,?_⟩
    simp only [factorCoordinates_index]
    have hd := cyclicEdge_decodes (by omega) d S ho f b t
    rw [ht,hx] at hd
    exact sameEdge_trans (Or.inl hd) ha
  unique i t j u hij := by
    have hi := cyclicEdge_decodes (by omega) d S ho (factorCoordinates i).1 (factorCoordinates i).2 t
    have hj := cyclicEdge_decodes (by omega) d S ho (factorCoordinates j).1 (factorCoordinates j).2 u
    rw [hi,hj] at hij
    have h3 : 3≤2^e := by
      have hp := Nat.pow_le_pow_right (show 1≤2 by decide) he
      omega
    obtain ⟨hf,hl⟩ := familyDecode_injective d h3 hij
    have hi' : S (factorCoordinates i).1 = S (factorCoordinates j).1 := congrArg S hf
    rw [hi'] at hl
    obtain ⟨hb,hv⟩ := labels_unique (Nat.two_pow_pos e) (S (factorCoordinates j).1) hl
    rw [hb] at hv
    have htu := profileCycles_injective (by omega) (S (factorCoordinates j).1)
      (ho (factorCoordinates j).1) (factorCoordinates j).2 hv
    have hh := congrArg factorIndex (Prod.ext hf hb)
    rw [factorIndex_coordinates,factorIndex_coordinates] at hh
    exact ⟨hh,htu⟩

/-- Transport an actual product factorization through the checked binary cube
isomorphism, including exact edge cover and cyclic-position uniqueness. -/
def cubeTransport {n m N : Nat} {hN : 0<N}
    (d : DecompositionData (ErdePaths.Vertex n × ErdePaths.Vertex n)
      (ProductAdjacent (@ErdePaths.Adjacent n)) m N hN) :
    DecompositionData (ErdePaths.Vertex (n+n)) (@ErdePaths.Adjacent (n+n)) m N hN where
  cycles i := {
    cycle := fun t => CubeProduct.encode ((d.cycles i).cycle t)
    position := fun v => (d.cycles i).position (CubeProduct.decode v)
    position_cycle := fun t => by rw [CubeProduct.decode_encode,(d.cycles i).position_cycle]
    cycle_position := fun v => by rw [(d.cycles i).cycle_position,CubeProduct.encode_decode]
    adjacent := fun t => by
      apply (CubeProduct.adjacent_iff _ _).mpr
      have hh := (d.cycles i).adjacent t
      rcases hh with hh | hh
      · exact Or.inr hh
      · exact Or.inl hh }
  symmetric := fun _ _ h => ErdePaths.adjacent_symm h
  loopfree := fun v h => ErdePaths.adjacent_ne h rfl
  cover u v huv := by
    have hp := (CubeProduct.adjacent_iff (CubeProduct.decode u) (CubeProduct.decode v)).mp
      (by simpa only [CubeProduct.encode_decode] using huv)
    have hprod : ProductAdjacent (@ErdePaths.Adjacent n) (CubeProduct.decode u) (CubeProduct.decode v) := by
      rcases hp with hp | hp
      · exact Or.inr hp
      · exact Or.inl hp
    obtain ⟨i,t,ht⟩ := d.cover _ _ hprod
    refine ⟨i,t,?_⟩
    have hm := SubdividedWiggle.map_sameEdge CubeProduct.encode ht
    simpa only [CubeProduct.encode_decode] using hm
  unique i t j s he := by
    have hm := SubdividedWiggle.map_sameEdge CubeProduct.decode he
    simp only [CubeProduct.decode_encode] at hm
    exact d.unique i t j s hm

/-- Fresh independently chosen positive profiles give a genuine factorization
of the actual doubled binary cube, not merely individual spanning tours. -/
noncomputable def cubeProfiles {n m : Nat} (hn : 2≤n)
    (d : DecompositionData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) m (2^n) (Nat.two_pow_pos n))
    (S : Fin m → Fin (2^n) → Bool) (ho : ∀ f, cardinality (S f)%2=1) :
    DecompositionData (ErdePaths.Vertex (n+n)) (@ErdePaths.Adjacent (n+n)) (2*m) ((2^n)*(2^n))
      (Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n)) :=
  cubeTransport (profiles hn d S ho)

/-- The newly constructed *actual factor clocks* retain the geometric SUM
residue used by source addressing. -/
theorem profiles_position_mod {V : Type} {R : V → V → Prop} {m e D : Nat}
    (he : 2≤e) (hd : D∣2^e) (d : DecompositionData V R m (2^e) (Nat.two_pow_pos e))
    (S : Fin m → Fin (2^e) → Bool) (ho : ∀ f, cardinality (S f)%2=1)
    (i : Fin (2*m)) (v : V×V) :
    (((profiles he d S ho).cycles i).position v).val%D =
      (((d.cycles (factorCoordinates i).1).position v.1).val+
        ((d.cycles (factorCoordinates i).1).position v.2).val)%D :=
  ProfileLift.clock_mod (by omega) hd (d.cycles (factorCoordinates i).1).toClockData
    (S (factorCoordinates i).1) (ho (factorCoordinates i).1) (factorCoordinates i).2 v

theorem cubeProfiles_position_mod {n m D : Nat} (hn : 2≤n) (hd : D∣2^n)
    (d : DecompositionData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) m (2^n) (Nat.two_pow_pos n))
    (S : Fin m → Fin (2^n) → Bool) (ho : ∀ f, cardinality (S f)%2=1)
    (i : Fin (2*m)) (v : ErdePaths.Vertex (n+n)) :
    (((cubeProfiles hn d S ho).cycles i).position v).val%D =
      (((d.cycles (factorCoordinates i).1).position (CubeProduct.decode v).1).val+
        ((d.cycles (factorCoordinates i).1).position (CubeProduct.decode v).2).val)%D :=
  profiles_position_mod hn hd d S ho i (CubeProduct.decode v)

#print axioms profiles_position_mod
#print axioms cubeProfiles
#print axioms cubeTransport
#print axioms profiles
#print axioms cyclicEdge_decodes
end ErdePaths.HamiltonProfile
