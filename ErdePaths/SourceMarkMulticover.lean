import ErdePaths.SourceBaselineCounts
import ErdePaths.SourceReciprocalExchange
import ErdePaths.DenseCodePairs
import ErdePaths.HamiltonCommonLast

namespace ErdePaths.SourceMarkMulticover
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts
attribute [local instance] Classical.propDecidable

/-- Actual Cartesian inverse coordinates test every physical image point. -/
theorem host_image_iff {U W : Type} {K A B : Nat}
    (G : ClockData U (K*A)) (H : ClockData W B) (P : AACTransition.Fine K A B→Prop) (v : U×W) :
    AACMarkExchange.ImageSet (ReciprocalEndpoints.host G H) P v ↔ P (G.position v.1,H.position v.2) := by
  constructor
  · rintro ⟨x,hx,hp⟩
    have he : x=(G.position v.1,H.position v.2) := by
      rw [←hx]
      simp only [ReciprocalEndpoints.host,G.position_cycle,H.position_cycle]
    exact he ▸ hp
  · intro hp
    refine ⟨(G.position v.1,H.position v.2),?_,hp⟩
    simp only [ReciprocalEndpoints.host,G.cycle_position,H.cycle_position]

section Source
variable {V W : Type} {e u B b : Nat}
variable (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
variable (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r))

noncomputable def markSet (H : Bool→Address (a+h)→ClockData W B) (post : Bool)
    (eps : Bool) (address : Address (a+h)) (v : VertexPower (VertexPower V a×VertexPower V a) h×W) : Prop :=
  let G := SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance eps address z
  let hK := Nat.two_pow_pos (e*2^(a+h+1)-r)
  let t := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
    (TurnPatterns.anti (L:=2^(a+h+1-r)) b)
  AACMarkExchange.ImageSet (ReciprocalEndpoints.host G (H eps address))
    (AACMarkIntervals.IsMark hK (if post then AACInduction.turnsAfter hK t (B-1) else fun w=>t w.1) z) v

/-- Full baseline incidence of the actual physically embedded source family. -/
theorem baseline (H : Bool→Address (a+h)→ClockData W B)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    ((List.finRange (2^(a+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H false
        (epsilonOf r q) (addressOf r q) v))).sum=b := by
  have hf : (fun q : Fin (2^(a+h+1))=>AACMarkExchange.incidence
      (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H false
        (epsilonOf r q) (addressOf r q) v))=
      (fun q=>if AACMarkIntervals.IsMark (Nat.two_pow_pos (e*2^(a+h+1)-r))
        (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
          (TurnPatterns.anti (L:=2^(a+h+1-r)) b) w.1) z
        ((SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance
          (epsilonOf r q) (addressOf r q) z).position v.1,
          (H (epsilonOf r q) (addressOf r q)).position v.2) then 1 else 0) := by
    funext q
    simp only [markSet,Bool.false_eq_true,ite_false,AACMarkExchange.incidence,host_image_iff]
  rw [hf]
  exact SourceBaselineCounts.baseline_incidence he C a h r hr hh room hA S ho hbalance hb hodd z v.1
    (fun q=>(H (epsilonOf r q) (addressOf r q)).position v.2)

/-- Exact full post-merger geometric multicover, derived from actual code
endpoints, literal reciprocal surgeries and a proved complete pair enumeration. -/
theorem postflip (hB : 0<B) (H : Bool→Address (a+h)→ClockData W B)
    (hlast : ∀address, (H true address).cycle ⟨B-1,by omega⟩=(H false address).cycle ⟨B-1,by omega⟩)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    ((List.finRange (2^(a+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true
        (epsilonOf r q) (addressOf r q) v))).sum=b := by
  have hp (address : Address (a+h)) :
      AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true false address v)+
      AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true true address v)=
      AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H false false address v)+
      AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H false true address v) := by
    have hh := SourceReciprocalExchange.anti_preservation he C a h r hr hh room hA S ho hbalance address
      hB (H true address) (H false address) (hlast address) z hb hodd v
    simpa only [markSet,ite_true,Bool.false_eq_true,ite_false,Nat.add_comm] using hh
  rw [DenseCodePairs.aggregate_exchange r hr
    (fun eps address=>AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true eps address v))
    (fun eps address=>AACMarkExchange.incidence (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H false eps address v)) hp]
  exact baseline he C a h r hr hh room hA S ho hbalance z H hb hodd v

/-- Genuine H Hamilton factors are normalized internally to one last vertex,
so the full postflip source multicover needs no shared-endpoint premise. -/
theorem normalized_postflip {R : W→W→Prop} {m : Nat} (hB : 0<B)
    (D : HamiltonData.DecompositionData W R m B hB) (last : W)
    (assigned : Bool→Address (a+h)→Fin m)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    let H := fun eps address=>((HamiltonCommonLast.normalize D last).cycles (assigned eps address)).toClockData
    ((List.finRange (2^(a+h+1))).map (fun q=>AACMarkExchange.incidence
      (markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true
        (epsilonOf r q) (addressOf r q) v))).sum=b := by
  dsimp only
  apply postflip he C a h r hr hh room hA S ho hbalance z hB _ _ hb hodd v
  intro address
  exact (HamiltonCommonLast.last_vertex D last (assigned true address)).trans
    (HamiltonCommonLast.last_vertex D last (assigned false address)).symm

end Source
#print axioms normalized_postflip
#print axioms postflip
end ErdePaths.SourceMarkMulticover
