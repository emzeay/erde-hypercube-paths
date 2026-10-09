import ErdePaths.SourceCodeOrigins
import ErdePaths.ReciprocalEndpoints

namespace ErdePaths.SourceReciprocalExchange
open SourceClock SourceProfile SourceCodeOrigins PairedArc SquareLift HierarchicalDecode

/-- Transport an actual arc only along proved cycle-length and arc-length
identities. The physical vertices and exact cyclic steps are retained. -/
def castArc {V : Type} {M N A B : Nat} (hMN : M=N) (hAB : A=B)
    (hM : 0<M) (hN : 0<N) (C : ClockData V M) (p : DirectedArc hM C A) :
    DirectedArc hN (castClock hMN C) B := by
  cases hMN
  cases hAB
  exact p

theorem castArc_zero {V : Type} {M N A B : Nat} (hMN : M=N) (hAB : A=B)
    (hM : 0<M) (hN : 0<N) (C : ClockData V M) (p : DirectedArc hM C A) :
    (castArc hMN hAB hM hN C p).vertex ⟨0,by omega⟩=p.vertex ⟨0,by omega⟩ := by
  cases hMN; cases hAB; rfl

theorem castArc_last {V : Type} {M N A B : Nat} (hMN : M=N) (hAB : A=B)
    (hM : 0<M) (hN : 0<N) (C : ClockData V M) (p : DirectedArc hM C A) :
    (castArc hMN hAB hM hN C p).vertex ⟨B,by omega⟩=p.vertex ⟨A,by omega⟩ := by
  cases hMN; cases hAB; rfl

theorem castClock_position_eq {V : Type} {M N : Nat} (hMN : M=N) (C : ClockData V M) (v : V) :
    (castClock hMN C).position v=Fin.cast hMN (C.position v) := by cases hMN; rfl

theorem threshold_eq {K A : Nat} (hK : 0<K) (z : Fin A) :
    BaselinePhysical.threshold hK z=AnchoredEmbedding.positionEncode (⟨0,hK⟩ : Fin K) z := by
  apply Fin.ext
  simp [BaselinePhysical.threshold,AnchoredEmbedding.positionEncode]

theorem anti_seams {K L b : Nat} (hK : 1<K) (hL : 0<L) (he : L%2=0)
    (hb : b<L) (ho : b%2=1) (hd : 2*L∣K) :
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) hL) (TurnPatterns.anti (L:=L) b)
    t ⟨0,by omega⟩=false ∧ t ⟨1,hK⟩=false ∧ t (predecessor (by omega) ⟨0,by omega⟩)=true := by
  dsimp only
  have hL2 : 1<L := by omega
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.anti_zero hL
  constructor
  · unfold TurnPatterns.repeated
    have hh : (⟨1%(2*L),Nat.mod_lt _ (Nat.mul_pos (by decide) hL)⟩ : Fin (2*L))=⟨1,by omega⟩ :=
      Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [hh]; exact TurnPatterns.anti_one hL2 (by omega)
  · have hp : predecessor (by omega) (⟨0,by omega⟩ : Fin K)=⟨K-1,by omega⟩ := by
      apply Fin.ext; simp [predecessor,Nat.mod_eq_of_lt (show K-1<K by omega)]
    rw [hp,TurnPatterns.repeated_last _ (by omega) hd]
    exact TurnPatterns.anti_last hL hb he ho

section Source
variable {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
  (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
  (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
  (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
  (address : Address (a+h))

local notation "K" => 2^(e*2^(a+h+1)-r)
local notation "A" => 2^r
local notation "hN" => Nat.mul_pos (Nat.two_pow_pos (e*2^(a+h+1)-r)) (Nat.two_pow_pos r)
local notation "raw" => fun eps => castClock (SourceLengths.fine_length he a h r hr) (SourceProfile.clock he C a h S ho eps address)
local notation "data" => family he C a h r hr hh room hA S ho hbalance address

/-- Actual false/true source arcs in the canonical fine coordinate length. -/
noncomputable def arc (eps : Bool) : DirectedArc hN (raw eps) A := by
  cases eps
  · exact castArc (SourceLengths.fine_length he a h r hr) hA _ hN _ (data).arcFalse
  · exact castArc (SourceLengths.fine_length he a h r hr) hA _ hN _ (data).arcTrue

theorem arc_start_equal :
    (arc he C a h r hr hh room hA S ho hbalance address false).vertex ⟨0,by omega⟩=
    (arc he C a h r hr hh room hA S ho hbalance address true).vertex ⟨0,by omega⟩ := by
  simp only [arc,castArc_zero]
  exact (data).start_equal

theorem arc_end_equal :
    (arc he C a h r hr hh room hA S ho hbalance address false).vertex ⟨A,by omega⟩=
    (arc he C a h r hr hh room hA S ho hbalance address true).vertex ⟨A,by omega⟩ := by
  simp only [arc,castArc_last]
  exact (data).end_equal

/-- The actual true oriented source is precisely the paired-arc forward
clock, with full occurrence origin equal to true arc END minus threshold. -/
theorem true_clock (z : Fin A) :
    orientedSource he C a h r hr hh room hA S ho hbalance true address z=
    ReciprocalEndpoints.forwardClock hN (raw true)
      (arc he C a h r hr hh room hA S ho hbalance address true)
      (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [orientedSource,ReciprocalEndpoints.forwardClock,OrientedClock.index,
    Bool.not_true,Bool.false_eq_true,ite_false,endpoint,ite_true,arc,castArc_last,castClock_position_eq,threshold_eq]

/-- The actual false oriented source is precisely the paired-arc reverse
clock, with full occurrence origin equal to false arc START plus threshold. -/
theorem false_clock (z : Fin A) :
    orientedSource he C a h r hr hh room hA S ho hbalance false address z=
    ReciprocalEndpoints.reverseClock hN (raw false)
      (arc he C a h r hr hh room hA S ho hbalance address false)
      (AnchoredEmbedding.positionEncode (⟨0,Nat.two_pow_pos _⟩ : Fin K) z) := by
  simp only [orientedSource,ReciprocalEndpoints.reverseClock,OrientedClock.index,
    Bool.not_false,endpoint,Bool.false_eq_true,ite_false,ite_true,arc,castArc_zero,castClock_position_eq,threshold_eq]

/-- Literal paired-source postflip preservation. The arcs are selected by
the proved SourceCodeOrigins family; physical endpoint coincidence and all
exchanged image sets are derived, never supplied as preservation inputs. -/
theorem preservation {W : Type} {B : Nat} (hB : 0<B) (H J : ClockData W B)
    (hlast : H.cycle ⟨B-1,by omega⟩=J.cycle ⟨B-1,by omega⟩) (z : Fin A)
    (t t' : Fin K→Bool)
    (ht0 : t ⟨0,Nat.two_pow_pos _⟩=false)
    (ht1 : t ⟨1,by have := SourceLengths.coarse_size he a h r hr; omega⟩=false)
    (htlast : t (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true)
    (ht0' : t' ⟨0,Nat.two_pow_pos _⟩=false)
    (ht1' : t' ⟨1,by have := SourceLengths.coarse_size he a h r hr; omega⟩=false)
    (htlast' : t' (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    let F := orientedSource he C a h r hr hh room hA S ho hbalance true address z
    let G := orientedSource he C a h r hr hh room hA S ho hbalance false address z
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host F H)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (AACInduction.turnsAfter (Nat.two_pow_pos _) t (B-1)) z) v)+
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host G J)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (AACInduction.turnsAfter (Nat.two_pow_pos _) t' (B-1)) z) v)=
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host F H)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w => t w.1) z) v)+
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host G J)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w => t' w.1) z) v) := by
  dsimp only
  rw [true_clock he C a h r hr hh room hA S ho hbalance address z,
    false_clock he C a h r hr hh room hA S ho hbalance address z]
  exact ReciprocalEndpoints.preservation
    (show 1<K by have := SourceLengths.coarse_size he a h r hr; omega)
    (Nat.two_pow_pos r) hB (raw true) (raw false)
    (arc he C a h r hr hh room hA S ho hbalance address true)
    (arc he C a h r hr hh room hA S ho hbalance address false)
    (arc_start_equal he C a h r hr hh room hA S ho hbalance address).symm
    (arc_end_equal he C a h r hr hh room hA S ho hbalance address).symm
    H J hlast z t t' ht0 ht1 htlast ht0' ht1' htlast' v

/-- Canonical antiL actual-source preservation with every turn-seam premise
discharged from the explicit uniform word and checked source length lemmas. -/
theorem anti_preservation {W : Type} {B b : Nat} (hB : 0<B) (H J : ClockData W B)
    (hlast : H.cycle ⟨B-1,by omega⟩=J.cycle ⟨B-1,by omega⟩) (z : Fin A)
    (hb : b<2^(a+h+1-r)) (hbodd : b%2=1)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
      (TurnPatterns.anti (L:=2^(a+h+1-r)) b)
    let F := orientedSource he C a h r hr hh room hA S ho hbalance true address z
    let G := orientedSource he C a h r hr hh room hA S ho hbalance false address z
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host F H)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (AACInduction.turnsAfter (Nat.two_pow_pos _) t (B-1)) z) v)+
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host G J)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (AACInduction.turnsAfter (Nat.two_pow_pos _) t (B-1)) z) v)=
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host F H)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w => t w.1) z) v)+
    AACMarkExchange.incidence (AACMarkExchange.ImageSet (ReciprocalEndpoints.host G J)
      (AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w => t w.1) z) v) := by
  dsimp only
  have hseam := anti_seams (show 1<K by have := SourceLengths.coarse_size he a h r hr; omega)
    (Nat.two_pow_pos (a+h+1-r)) (SourceLengths.block_even a h r hr)
    hb hbodd (SourceLengths.coarse_period he a h r hr)
  exact preservation he C a h r hr hh room hA S ho hbalance address hB H J hlast z _ _
    hseam.1 hseam.2.1 hseam.2.2 hseam.1 hseam.2.1 hseam.2.2 v

end Source
#print axioms anti_preservation
#print axioms preservation
#print axioms arc_start_equal
#print axioms true_clock
#print axioms false_clock
end ErdePaths.SourceReciprocalExchange
