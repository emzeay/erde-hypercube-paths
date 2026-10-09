import ErdePaths.ProfileArcs
import ErdePaths.CubeCycle

namespace ErdePaths.ProfileLift
open SquareLift SourceClock Profile ProfileArcs SubdividedWiggle

variable {V : Type} {e : Nat}

def map (C : ClockData V (2^e)) (u : Profile.Vertex (2^e)) : V×V :=
  (C.cycle u.1,C.cycle u.2)
def unmap (C : ClockData V (2^e)) (v : V×V) : Profile.Vertex (2^e) :=
  (C.position v.1,C.position v.2)

theorem unmap_map (C : ClockData V (2^e)) (u : Profile.Vertex (2^e)) : unmap C (map C u)=u := by
  simp only [unmap,map,C.position_cycle]
theorem map_unmap (C : ClockData V (2^e)) (v : V×V) : map C (unmap C v)=v := by
  simp only [unmap,map,C.cycle_position]
theorem map_injective (C : ClockData V (2^e)) : Function.Injective (map C) := by
  intro u v he
  have hh := congrArg (unmap C) he
  simpa only [unmap_map] using hh

/-- A fresh positive profile is lifted through the actual parent coordinates. -/
noncomputable def clock (he : 1≤e) (C : ClockData V (2^e)) (S : Fin (2^e) → Bool)
    (hodd : cardinality S%2=1) (color : Bool) : ClockData (V×V) ((2^e)*(2^e)) where
  cycle t := map C ((profileClockData he S hodd color).cycle t)
  position v := (profileClockData he S hodd color).position (unmap C v)
  position_cycle t := by rw [unmap_map,(profileClockData he S hodd color).position_cycle]
  cycle_position v := by rw [(profileClockData he S hodd color).cycle_position,map_unmap]

/-- Genuine physical inverse clocks have SUM residues at every parent modulus. -/
theorem clock_mod {D : Nat} (he : 1≤e) (hD : D∣2^e) (C : ClockData V (2^e))
    (S : Fin (2^e) → Bool) (hodd : cardinality S%2=1) (color : Bool) (v : V×V) :
    ((clock he C S hodd color).position v).val%D=
      ((C.position v.1).val+(C.position v.2).val)%D := by
  exact profileClock_mod he hD S hodd color (unmap C v)

/-- Both profile twins and entire common-clock source families share the
physical SUM residue; the profile selector never creates an unproved bit. -/
theorem common_clock {D : Nat} (he : 1≤e) (hD : D∣2^e)
    (C C' : ClockData V (2^e))
    (hc : ∀ v, (C.position v).val%D=(C'.position v).val%D)
    (S T : Fin (2^e) → Bool) (hs : cardinality S%2=1) (ht : cardinality T%2=1)
    (color color' : Bool) (v : V×V) :
    ((clock he C S hs color).position v).val%D=
      ((clock he C' T ht color').position v).val%D := by
  rw [clock_mod he hD,clock_mod he hD]
  simp only [Nat.add_mod,Nat.mod_mod,hc]

private theorem map_decode (C : ClockData V (2^e)) (a : TorusEdgeLabel (2^e)) :
    (map C (decode (Nat.two_pow_pos e) (fun t => t) a).1,
      map C (decode (Nat.two_pow_pos e) (fun t => t) a).2)=
        decode (Nat.two_pow_pos e) C.cycle a := by
  cases a <;> rfl

/-- Actual profile edges remain genuine Cartesian edges of the parent graph. -/
theorem mapped_adjacent {R : V → V → Prop}
    (C : HamiltonData.CycleData V R (2^e) (Nat.two_pow_pos e))
    (hR : ∀ u v, R u v → R v u) {u v : Profile.Vertex (2^e)}
    (h : TorusAdjacent (Nat.two_pow_pos e) u v) :
    ProductAdjacent R (map C.toClockData u) (map C.toClockData v) := by
  obtain ⟨a,ha⟩ := h
  have hm := map_sameEdge (map C.toClockData) ha
  rw [map_decode] at hm
  have hd := decode_adjacent (Nat.two_pow_pos e) C.adjacent a
  rcases hm with hm | hm
  · have hu := congrArg Prod.fst hm
    have hv := congrArg Prod.snd hm
    simpa only [hu,hv] using hd
  · have hv := congrArg Prod.fst hm
    have hu := congrArg Prod.snd hm
    simpa only [hu,hv] using productAdjacent_symm hR hd

/-- Profile clocks themselves, with actual ambient adjacency, not only a
numeric permutation. Global torus/factor ownership is a separate theorem. -/
noncomputable def cycle {R : V → V → Prop} (he : 1≤e)
    (C : HamiltonData.CycleData V R (2^e) (Nat.two_pow_pos e))
    (hR : ∀ u v, R u v → R v u) (S : Fin (2^e) → Bool)
    (hodd : cardinality S%2=1) (color : Bool) :
    HamiltonData.CycleData (V×V) (ProductAdjacent R) ((2^e)*(2^e))
      (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) where
  toClockData := clock he C.toClockData S hodd color
  adjacent t := mapped_adjacent C hR (profileCycles_adjacent (Nat.two_pow_pos e) S color t)

/-- Literal common arcs are transported through actual parent vertices. -/
def liftedArc {A : Nat} (C : ClockData V (2^e)) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (color : Bool) (i : Fin (A+1)) : V×V :=
  map C (arc (Nat.two_pow_pos e) hA S color i)

theorem liftedArc_simple {A : Nat} (he : 1≤e) (C : ClockData V (2^e)) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (hodd : cardinality S%2=1) (color : Bool) :
    Function.Injective (liftedArc C hA S color) := by
  intro i j heq
  exact arc_simple he hA S hodd color (map_injective C heq)

theorem liftedArc_adjacent {R : V → V → Prop} {A : Nat}
    (C : HamiltonData.CycleData V R (2^e) (Nat.two_pow_pos e))
    (hR : ∀ u v, R u v → R v u) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (color : Bool) (i : Fin A) :
    ProductAdjacent R (liftedArc C.toClockData hA S color i.castSucc)
      (liftedArc C.toClockData hA S color i.succ) :=
  mapped_adjacent C hR (arc_adjacent (Nat.two_pow_pos e) hA S color i)

theorem liftedArc_clock {A : Nat} (he : 1≤e) (C : ClockData V (2^e)) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (hodd : cardinality S%2=1) (color : Bool) (i : Fin (A+1)) :
    (clock he C S hodd color).position (liftedArc C hA S color i)=arcIndex (Nat.two_pow_pos e) hA i := by
  change (profileClockData he S hodd color).position
    (unmap C (map C (arc (Nat.two_pow_pos e) hA S color i)))=_
  rw [unmap_map]
  exact arc_clock he hA S hodd color i

/-- Lifted complementary arcs meet at their literal common physical endpoint. -/
theorem liftedArc_balanced_end {u : Nat} (C : ClockData V (2^e)) (hu : 2*u<2^e)
    (S : Fin (2^e) → Bool) (hp : prefixCount S (2*u)=u) (color : Bool) :
    liftedArc C hu S color (Fin.last (2*u))=
      (C.cycle ⟨u,by omega⟩,C.cycle ⟨u,by omega⟩) := by
  unfold liftedArc
  rw [arc_balanced_end (Nat.two_pow_pos e) hu S hp color]
  rfl

/-- Literal transport to the genuine binary cube, using the checked product
isomorphism. This creates actual fresh profile Hamilton cycles in Q_(n+n). -/
noncomputable def cubeCycle {n : Nat} (hn : 1≤n)
    (C : HamiltonData.CycleData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) (2^n) (Nat.two_pow_pos n))
    (S : Fin (2^n) → Bool) (hodd : cardinality S%2=1) (color : Bool) :
    HamiltonData.CycleData (ErdePaths.Vertex (n+n)) (@ErdePaths.Adjacent (n+n)) ((2^n)*(2^n))
      (Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos n)) where
  cycle t := CubeProduct.encode ((cycle hn C (fun _ _ h => adjacent_symm h) S hodd color).cycle t)
  position v := (cycle hn C (fun _ _ h => adjacent_symm h) S hodd color).position (CubeProduct.decode v)
  position_cycle t := by rw [CubeProduct.decode_encode,(cycle hn C _ S hodd color).position_cycle]
  cycle_position v := by rw [(cycle hn C _ S hodd color).cycle_position,CubeProduct.encode_decode]
  adjacent t := by
    apply (CubeProduct.adjacent_iff _ _).mpr
    have hh := (cycle hn C (fun _ _ h => adjacent_symm h) S hodd color).adjacent t
    rcases hh with h | h
    · exact Or.inr h
    · exact Or.inl h

def cubeArc {n A : Nat}
    (C : HamiltonData.CycleData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) (2^n) (Nat.two_pow_pos n))
    (hA : A<2^n) (S : Fin (2^n) → Bool) (color : Bool) (i : Fin (A+1)) :
    ErdePaths.Vertex (n+n) := CubeProduct.encode (liftedArc C.toClockData hA S color i)

theorem cubeArc_simple {n A : Nat} (hn : 1≤n)
    (C : HamiltonData.CycleData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) (2^n) (Nat.two_pow_pos n))
    (hA : A<2^n) (S : Fin (2^n) → Bool) (hodd : cardinality S%2=1) (color : Bool) :
    Function.Injective (cubeArc C hA S color) := by
  intro i j he
  exact liftedArc_simple hn C.toClockData hA S hodd color (CubeProduct.encode_injective he)

theorem cubeArc_adjacent {n A : Nat}
    (C : HamiltonData.CycleData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) (2^n) (Nat.two_pow_pos n))
    (hA : A<2^n) (S : Fin (2^n) → Bool) (color : Bool) (i : Fin A) :
    ErdePaths.Adjacent (cubeArc C hA S color i.castSucc) (cubeArc C hA S color i.succ) := by
  apply (CubeProduct.adjacent_iff _ _).mpr
  have hh := liftedArc_adjacent C (fun _ _ h => adjacent_symm h) hA S color i
  rcases hh with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem cubeArc_clock {n A : Nat} (hn : 1≤n)
    (C : HamiltonData.CycleData (ErdePaths.Vertex n) (@ErdePaths.Adjacent n) (2^n) (Nat.two_pow_pos n))
    (hA : A<2^n) (S : Fin (2^n) → Bool) (hodd : cardinality S%2=1) (color : Bool) (i : Fin (A+1)) :
    (cubeCycle hn C S hodd color).position (cubeArc C hA S color i)=arcIndex (Nat.two_pow_pos n) hA i := by
  change (clock hn C.toClockData S hodd color).position
    (CubeProduct.decode (CubeProduct.encode (liftedArc C.toClockData hA S color i)))=_
  rw [CubeProduct.decode_encode]
  exact liftedArc_clock hn C.toClockData hA S hodd color i

#print axioms cubeCycle
#print axioms cubeArc_clock
#print axioms clock
#print axioms common_clock
#print axioms cycle
#print axioms liftedArc_simple
#print axioms liftedArc_clock
#print axioms liftedArc_balanced_end
end ErdePaths.ProfileLift
