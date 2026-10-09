import ErdePaths.PairedArcTower
import ErdePaths.SourceProfile

namespace ErdePaths.SourcePairedArcs
open SourceClock SourceProfile PairedArc Profile HierarchicalDecode

/-- The final arc lives in the literal lower/profile/upper source clock,
not an independently supplied factor clock. -/
def Paired {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h A D : Nat) (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (address : Address (a+h)) (c : Fin D) : Prop :=
  ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
      (SourceProfile.clock he C a h S ho false address) A,
  ∃q' : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
      (SourceProfile.clock he C a h S ho true address) A,
    q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
    q.vertex ⟨A,by omega⟩=q'.vertex ⟨A,by omega⟩ ∧
    ∀i, ((SourceProfile.clock he C a h S ho false address).position (q.vertex i)).val%D=(c.val+i.val)%D ∧
      ((SourceProfile.clock he C a h S ho true address).position (q'.vertex i)).val%D=(c.val+i.val)%D

/-- Actual source-profile paired arcs at every positive upper depth. The
prefix length cast and both address lookups are the source definitions. -/
theorem paired {V : Type} {e u D : Nat} (he : 2≤e) (hD : 0<D)
    (C : ClockData V (2^e)) (a h : Nat) (hh : 0<h)
    (room : D∣lengthPower (2^e) a) (hshort : 2*u<D)
    (S : Address a → Fin (2^(e*2^a)) → Bool)
    (ho : ∀ address, cardinality (S address)%2=1)
    (address : Address (a+h))
    (hbalance : prefixCount (S (lowerAddress address)) (2*u)=u) (c : Fin D) :
    Paired he C a h (2*u) D S ho address c := by
  have hex : 2≤e*2^a := by have := exponent_bound he a; omega
  have hd : D∣2^(e*2^a) := by simpa only [lengthPower_pow] using room
  have hdn : D≤2^(e*2^a) := Nat.le_of_dvd (Nat.two_pow_pos _) hd
  have hu : 2*u<2^(e*2^a) := Nat.lt_of_lt_of_le hshort hdn
  cases h with
  | zero => omega
  | succ k =>
    exact PairedArcTower.profile_paired_tower (by omega) hD hd hu hshort
      (PairedArcTower.profile_room hex hd)
      (prefixClock C a (lowerAddress address)) (S (lowerAddress address))
      (ho (lowerAddress address)) hbalance k (upperAddress address) c

/-- Literal uniform interval selector, with oddness and balanced prefix
proved from the numeric half-length, at each actual lower address. -/
theorem interval {V : Type} {e u D : Nat} (he : 2≤e) (hD : 0<D)
    (C : ClockData V (2^e)) (a h : Nat) (hh : 0<h)
    (room : D∣lengthPower (2^e) a) (hshort : 2*u<D) (huEven : u%2=0)
    (address : Address (a+h)) (c : Fin D) :
    let S : Address a → Fin (2^(e*2^a)) → Bool := fun _ => intervalWithEndpoint u
    let hu : 2*u<2^(e*2^a) := Nat.lt_of_lt_of_le hshort
      (Nat.le_of_dvd (Nat.two_pow_pos _) (by simpa only [lengthPower_pow] using room))
    let ho : ∀ address, cardinality (S address)%2=1 := fun _ => intervalWithEndpoint_odd hu huEven
    Paired he C a h (2*u) D S ho address c := by
  intro S hu ho
  exact paired he hD C a h hh room hshort S ho address
    (intervalWithEndpoint_balanced_prefix hu) c

/-- Two-edge arcs use the genuine singleton selector, including its numeric
odd cardinality and one-step-per-coordinate prefix balance. -/
theorem singleton {V : Type} {e D : Nat} (he : 2≤e) (hD : 0<D)
    (C : ClockData V (2^e)) (a h : Nat) (hh : 0<h)
    (room : D∣lengthPower (2^e) a) (hshort : 2<D)
    (address : Address (a+h)) (c : Fin D) :
    let S : Address a → Fin (2^(e*2^a)) → Bool := fun _ => intervalWithEndpoint 0
    let ho : ∀ address, cardinality (S address)%2=1 := fun _ =>
      intervalWithEndpoint_odd (by have := Nat.two_pow_pos (e*2^a); omega) rfl
    Paired he C a h 2 D S ho address c := by
  intro S ho
  have hex : 2≤e*2^a := by have := exponent_bound he a; omega
  have h4 : 4≤2^(e*2^a) := by
    have hh := Nat.pow_le_pow_right (show 1≤2 by decide) hex
    omega
  have hp : prefixCount (S (lowerAddress address)) (2*1)=1 := by
    change prefixCount (intervalWithEndpoint (N:=2^(e*2^a)) 0) 2=1
    rw [intervalWithEndpoint_prefix 0 2 (by omega)]
    rfl
  exact paired (u:=1) he hD C a h hh room hshort S ho address hp c

#print axioms paired
#print axioms interval
#print axioms singleton
end ErdePaths.SourcePairedArcs
