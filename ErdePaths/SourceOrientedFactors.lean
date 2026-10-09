import ErdePaths.SourceFactors
import ErdePaths.SourceCodeOrigins
import ErdePaths.HamiltonOrient

namespace ErdePaths.SourceOrientedFactors
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift

/-- Decode every actual owned factor into its complete source configuration. -/
noncomputable def configuration {m : Nat} (a h : Nat) (q : Fin (count (2*count m a) h)) :
    Fin m×Bool×Address (a+h) :=
  let hf := SourceFactors.index_surjective a h q
  (Classical.choose hf,Classical.choose (Classical.choose_spec hf),
    Classical.choose (Classical.choose_spec (Classical.choose_spec hf)))

theorem configuration_index {m : Nat} (a h : Nat) (q : Fin (count (2*count m a) h)) :
    SourceFactors.index a h (configuration a h q).1 (configuration a h q).2.1
      (configuration a h q).2.2=q :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (SourceFactors.index_surjective a h q)))

theorem index_configuration {m : Nat} (a h : Nat) (f : Fin m) (eps : Bool) (address : Address (a+h)) :
    configuration a h (SourceFactors.index a h f eps address)=(f,eps,address) := by
  have hi := configuration_index a h (SourceFactors.index a h f eps address)
  obtain ⟨hf,he,ha⟩ := SourceFactors.index_injective a h _ _ _ _ _ _ hi
  exact Prod.ext hf (Prod.ext he ha)

section Factors
variable {V : Type} {R : V→V→Prop} {m e u : Nat}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
  (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
  (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
  (ho : ∀f address, Profile.cardinality (S f address)%2=1)
  (hbalance : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)

local notation "K" => 2^(e*2^(a+h+1)-r)
local notation "A" => 2^r

/-- Canonical length transport of the actual full source-family partition. -/
noncomputable def base :
    DecompositionData (VertexPower (VertexPower V a×VertexPower V a) h)
      (relation (ProductAdjacent (relation R a)) h) (count (2*count m a) h)
      (K*A) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) :=
  SourceFactors.castDecomposition (SourceLengths.fine_length he a h r hr)
    (SourceFactors.family D he a h S ho)

/-- Literal actual occurrence origins prescribed by the constructed source
paired arcs, decoded in the original initial-factor and Boolean addresses. -/
noncomputable def startsFor (z : Fin A) (cfg : Fin m×Bool×Address (a+h)) : Fin (K*A) :=
  let data := SourceCodeOrigins.family he (D.cycles cfg.1).toClockData a h r hr hh room hA
    (S cfg.1) (ho cfg.1) (hbalance cfg.1) cfg.2.2
  OrientedClock.index (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
    (Fin.cast (SourceLengths.fine_length he a h r hr) (SourceCodeOrigins.endpoint data cfg.2.1))
    (!cfg.2.1) (BaselinePhysical.threshold (Nat.two_pow_pos _) z)

noncomputable def starts (z : Fin A) (q : Fin (count (2*count m a) h)) : Fin (K*A) :=
  startsFor D he a h r hr hh room hA S ho hbalance z (configuration a h q)

noncomputable def directions (q : Fin (count (2*count m a) h)) : Bool := (configuration a h q).2.1

/-- Genuine full source-factor graph partition at the prescribed origins
and twin orientations; edge cover/uniqueness come from actual constructors. -/
noncomputable def factors (z : Fin A) :
    DecompositionData (VertexPower (VertexPower V a×VertexPower V a) h)
      (relation (ProductAdjacent (relation R a)) h) (count (2*count m a) h)
      (K*A) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) :=
  HamiltonOrient.factors (base D he a h r hr S ho)
    (starts D he a h r hr hh room hA S ho hbalance z) (directions a h)

/-- The actual OWNED factor clock at each complete source configuration is
exactly the canonical orientedSource, not an independently supplied cycle. -/
theorem clock_eq (z : Fin A) (f : Fin m) (eps : Bool) (address : Address (a+h)) :
    ((factors D he a h r hr hh room hA S ho hbalance z).cycles
      (SourceFactors.index a h f eps address)).toClockData=
    SourceCodeOrigins.orientedSource he (D.cycles f).toClockData a h r hr hh room hA
      (S f) (ho f) (hbalance f) eps address z := by
  unfold factors HamiltonOrient.factors
  change OrientedClock.clock _
    (((base D he a h r hr S ho).cycles (SourceFactors.index a h f eps address)).toClockData)
    (starts D he a h r hr hh room hA S ho hbalance z (SourceFactors.index a h f eps address))
    (directions a h (SourceFactors.index a h f eps address))=_
  unfold starts directions
  rw [index_configuration]
  unfold base
  rw [SourceFactors.castDecomposition_clock,SourceFactors.clock_eq]
  rfl

end Factors
#print axioms factors
#print axioms clock_eq
#print axioms configuration_index
#print axioms index_configuration
end ErdePaths.SourceOrientedFactors
