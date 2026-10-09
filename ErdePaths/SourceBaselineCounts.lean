import ErdePaths.SourceCodeOrigins
import ErdePaths.DenseSourceIncidence

namespace ErdePaths.SourceBaselineCounts
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts DenseSourceMarks
attribute [local instance] Classical.propDecidable

/-- Actual oriented source factors have exactly b-fold baseline geometric
mark incidence. Their code endpoints and all period/length transports are
constructed internally. Different H factors may supply arbitrary actual rows. -/
theorem baseline_incidence {V : Type} {e u B b : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1) (z : Fin (2^r))
    (v : VertexPower (VertexPower V a×VertexPower V a) h)
    (row : Fin (2^(a+h+1))→Fin B) :
    ((List.finRange (2^(a+h+1))).map (fun q=>
      if AACMarkIntervals.IsMark (Nat.two_pow_pos (e*2^(a+h+1)-r))
        (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
          (TurnPatterns.anti (L:=2^(a+h+1-r)) b) w.1) z
        ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance
          (epsilonOf r q) (addressOf r q) z).position v,row q) then 1 else 0)).sum=b := by
  have hf : (fun q : Fin (2^(a+h+1))=>
      if AACMarkIntervals.IsMark (Nat.two_pow_pos (e*2^(a+h+1)-r))
        (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
          (TurnPatterns.anti (L:=2^(a+h+1-r)) b) w.1) z
        ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance
          (epsilonOf r q) (addressOf r q) z).position v,row q) then 1 else 0)=
      (fun q=>if ∃i : Fin b, Marked he C a h r hr S ho (fun eps _=>!eps)
        (epsilonOf r q) (addressOf r q) i.val v then 1 else 0) := by
    funext q
    have hp := SourceCodeOrigins.canonical_classes he C a h r hr hh room hA S ho hbalance
      hb hodd (epsilonOf r q) (addressOf r q) z v (row q)
    simp only [hp]
  rw [hf]
  exact DenseSourceIncidence.exact_configuration_incidence he C a h r hr S ho room
    (fun eps _=>!eps) (by intros; rfl) b (Nat.le_of_lt hb) v

#print axioms baseline_incidence
end ErdePaths.SourceBaselineCounts
