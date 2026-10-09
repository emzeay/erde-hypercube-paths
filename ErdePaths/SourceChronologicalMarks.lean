import ErdePaths.SourceMarkMulticover
import ErdePaths.SourceOrientedFactors
import ErdePaths.AACPhysicalBalance
import ErdePaths.CubeHierarchy
import ErdePaths.ChordGraph

namespace ErdePaths.SourceChronologicalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts SquareLift
open AACTransition AACFine AACFineClock AACMarkIntervals
attribute [local instance] Classical.propDecidable

/-- Data chosen from the actual fine-Euler construction; no traversal or label
coverage is postulated by its constructor. -/
structure EulerData {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B) (t : Fin K→Bool) where
  orbit : AACMerge.Orbit (AACTransition.State K B)
    (transition hK hB (AACInduction.turnsAfter hK t (B-1)))
    (B*(2*K)) (Nat.mul_pos hB (by omega))
  length : (indexList (A:=A) orbit).length=K*B*(A+1)
  injective : Function.Injective (fineLabel hK hA hB orbit length)
  surjective : Function.Surjective (fineLabel hK hA hB orbit length)

noncomputable def euler {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (t : Fin K→Bool) (hb : AACTransition.BalancedTurns t) (ht : t ⟨0,hK⟩=false) : EulerData hK hA hB t :=
  Classical.choice (by
    obtain ⟨C,hE,⟨hi,hs⟩,_⟩ := numeric_fine_euler hK hA hB t hb ht
    exact ⟨⟨C,hE,hi,hs⟩⟩)

section Source
variable {V W : Type} {e u B b : Nat}
variable (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
variable (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r))
local notation "K" => 2^(e*2^(a+h+1)-r)
local notation "A" => 2^r

noncomputable def sourceEuler (hB : 0<B) :
    EulerData (Nat.two_pow_pos (e*2^(a+h+1)-r)) (Nat.two_pow_pos r) hB
      (TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.anti (L:=2^(a+h+1-r)) b)) :=
  euler _ _ hB _
    (TurnPatterns.repeated_anti_balanced (Nat.two_pow_pos _) (SourceLengths.coarse_period he a h r hr) b)
    ((TurnPatterns.repeated_zero _ _ _).trans (TurnPatterns.anti_zero (Nat.two_pow_pos _)))

noncomputable def word (hB : 0<B) (H : Bool→Address (a+h)→ClockData W B)
    (q : Fin (2^(a+h+1))) : List (VertexPower (VertexPower V a×VertexPower V a) h×W) :=
  let E := sourceEuler (b:=b) he a h r hr hB
  (markWord (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) z).map
      (AACFineGeometry.physical
        (SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance
          (epsilonOf r q) (addressOf r q) z) (H (epsilonOf r q) (addressOf r q)))

/-- Actual chronological word counts, rather than mark-set indicators. -/
theorem multiplicity [DecidableEq (VertexPower (VertexPower V a×VertexPower V a) h×W)]
    (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0) (hz : 0<z.val)
    (H : Bool→Address (a+h)→ClockData W B)
    (hlast : ∀address, (H true address).cycle ⟨B-1,by omega⟩=(H false address).cycle ⟨B-1,by omega⟩)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1)
    (v : VertexPower (VertexPower V a×VertexPower V a) h×W) :
    ((List.finRange (2^(a+h+1))).map (fun q=>
      (word (b:=b) he C a h r hr hh room hA S ho hbalance z hB H q).countP
        (fun w=>decide (w=v)))).sum=b := by
  have hK4 := SourceLengths.coarse_size he a h r hr
  have h3 : 3≤K*A := by
    have hm := Nat.mul_le_mul_left K (show 1≤A from Nat.two_pow_pos r)
    simp only [Nat.mul_one] at hm
    omega
  have hE2 : 2≤K*B*(A+1) := by
    have hp := Nat.two_pow_pos r
    have hm := Nat.mul_le_mul_right B hK4
    have hm' := Nat.mul_le_mul_left (K*B) (show 1≤A+1 by omega)
    omega
  have hf : (fun q : Fin (2^(a+h+1))=>
      (word (b:=b) he C a h r hr hh room hA S ho hbalance z hB H q).countP (fun w=>decide (w=v)))=
      (fun q=>AACMarkExchange.incidence
        (SourceMarkMulticover.markSet (b:=b) he C a h r hr hh room hA S ho hbalance z H true
          (epsilonOf r q) (addressOf r q) v)) := by
    funext q
    unfold word
    dsimp only
    have hc := AACMarkWord.physical_word_incidence (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB h3 hB3 hbeven
      (sourceEuler (b:=b) he a h r hr hB).orbit (sourceEuler (b:=b) he a h r hr hB).length
      (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) hE2
      (sourceEuler (b:=b) he a h r hr hB).injective
      (sourceEuler (b:=b) he a h r hr hB).surjective z hz
      (SourceCodeOrigins.orientedSource he C a h r hr hh room hA S ho hbalance
        (epsilonOf r q) (addressOf r q) z) (H (epsilonOf r q) (addressOf r q)) v
    simp only [SourceMarkMulticover.markSet,ite_true,AACMarkExchange.incidence,
      SourceMarkMulticover.host_image_iff]
    refine Eq.trans ?_ hc
    apply List.countP_congr
    intro w hw
    simp only [decide_eq_true_eq]
  rw [hf]
  exact SourceMarkMulticover.postflip he C a h r hr hh room hA S ho hbalance z hB H hlast hb hodd v

end Source
section Cube
variable {e d m u B b : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
variable (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
variable (ho : ∀f address, Profile.cardinality (S f address)%2=1)
variable (hbalance : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r))
local notation "K" => 2^(e*2^(a+h+1)-r)
local notation "A" => 2^r

/-- Actual binary parity of the physical Cartesian host, through literal
hierarchy coordinates. -/
def physicalParity (v : VertexPower (VertexPower (Vertex e) a×VertexPower (Vertex e) a) h×Vertex d) : Bool :=
  CubeParity.parity (CubeProduct.encode ((CubeHierarchy.sourceIso e a h).encode v.1,v.2))

/-- Chronological balance for every actual source factor. Graph adjacency
comes from the genuine source decomposition, then exact binary transport. -/
theorem balanced (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0) (hz : 0<z.val)
    (H : Bool→Address (a+h)→HamiltonData.CycleData (Vertex d) (@Adjacent d) B hB)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1) (f : Fin m) (q : Fin (2^(a+h+1))) :
    NoncrossingMatch.Balanced (physicalParity (e:=e) (d:=d) (a:=a) (h:=h))
      (word (b:=b) he (D.cycles f).toClockData a h r hr hh room hA (S f) (ho f) (hbalance f)
        z hB (fun eps address=>(H eps address).toClockData) q) := by
  let I := CubeHierarchy.sourceIso e a h
  let actual := CubeHierarchy.transport I
    (SourceOrientedFactors.factors D he a h r hr hh room hA S ho hbalance z)
  let F := actual.cycles (SourceFactors.index a h f (epsilonOf r q) (addressOf r q))
  let G := SourceCodeOrigins.orientedSource he (D.cycles f).toClockData a h r hr hh room hA
    (S f) (ho f) (hbalance f) (epsilonOf r q) (addressOf r q) z
  have hF (i : Fin (K*A)) : F.cycle i=I.encode (G.cycle i) := by
    have hc := SourceOrientedFactors.clock_eq D he a h r hr hh room hA S ho hbalance
      z f (epsilonOf r q) (addressOf r q)
    exact congrArg (fun T : ClockData _ (K*A)=>I.encode (T.cycle i)) hc
  have hK4 := SourceLengths.coarse_size he a h r hr
  have h3 : 3≤K*A := by
    have hm := Nat.mul_le_mul_left K (show 1≤A from Nat.two_pow_pos r)
    simp only [Nat.mul_one] at hm
    omega
  have hE2 : 2≤K*B*(A+1) := by
    have hm := Nat.mul_le_mul_right B hK4
    have hm' := Nat.mul_le_mul_left (K*B) (show 1≤A+1 by omega)
    omega
  have hseam := SourceReciprocalExchange.anti_seams
    (show 1<K by omega) (Nat.two_pow_pos (a+h+1-r))
    (SourceLengths.block_even a h r hr) hb hodd (SourceLengths.coarse_period he a h r hr)
  have ha : A%2=0 := Nat.mod_eq_zero_of_dvd ⟨u,by omega⟩
  let E := sourceEuler (b:=b) he a h r hr hB
  have hc := AACPhysicalBalance.chronological_physical_balanced
    (show 1<K by omega) (Nat.two_pow_pos r) hB h3 hB3 hbeven F (H (epsilonOf r q) (addressOf r q))
    ha _ hseam.1 hseam.2.1 hseam.2.2 (B-1) E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) hE2 E.injective E.surjective z hz
  have hw :
      (word (b:=b) he (D.cycles f).toClockData a h r hr hh room hA (S f) (ho f) (hbalance f)
        z hB (fun eps address=>(H eps address).toClockData) q).map
        (fun v=>CubeProduct.encode (I.encode v.1,v.2))=
      (markWord (Nat.two_pow_pos _) (Nat.two_pow_pos _) hB E.orbit E.length
        (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) z).map
        (fun v=>CubeProduct.encode (F.cycle v.1,(H (epsilonOf r q) (addressOf r q)).cycle v.2)) := by
    unfold word
    dsimp only
    rw [List.map_map]
    congr 1
    funext v
    dsimp only [Function.comp_def,AACFineGeometry.physical]
    rw [hF]
  rw [←hw] at hc
  unfold NoncrossingMatch.Balanced at hc ⊢
  simp only [List.countP_map,Function.comp_def] at hc
  exact hc

/-- Genuine actual chronological Marks at one initial parent, with normalized
H factors. Balance and multiplicity are both derived; neither is an input. -/
noncomputable def marks {M : Nat} (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0) (hz : 0<z.val)
    (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
    (last : Vertex d) (assigned : Bool→Address (a+h)→Fin M)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1) (f : Fin m) :
    ChordGraph.Marks
      (VertexPower (VertexPower (Vertex e) a×VertexPower (Vertex e) a) h×Vertex d)
      (physicalParity (e:=e) (d:=d) (a:=a) (h:=h)) (2^(a+h+1)) b where
  word := word (b:=b) he (D.cycles f).toClockData a h r hr hh room hA (S f) (ho f) (hbalance f)
    z hB (fun eps address=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps address)).toClockData)
  balanced := balanced D he a h r hr hh room hA S ho hbalance z hB hB3 hbeven hz
    (fun eps address=>(HamiltonCommonLast.normalize HD last).cycles (assigned eps address)) hb hodd f
  multiplicity v := multiplicity he (D.cycles f).toClockData a h r hr hh room hA (S f) (ho f) (hbalance f)
    z hB hB3 hbeven hz _
    (fun address=>(HamiltonCommonLast.last_vertex HD last (assigned true address)).trans
      (HamiltonCommonLast.last_vertex HD last (assigned false address)).symm) hb hodd v

end Cube
#print axioms balanced
#print axioms marks
#print axioms euler
#print axioms multiplicity
end ErdePaths.SourceChronologicalMarks
