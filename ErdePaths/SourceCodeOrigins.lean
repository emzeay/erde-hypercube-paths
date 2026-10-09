import ErdePaths.CodePairedArcs
import ErdePaths.SourcePhysicalMarks
import ErdePaths.SourceLengths

namespace ErdePaths.SourceCodeOrigins
open SourceClock SourceProfile PairedArc HierarchicalDecode SquareLift

/-- Concrete paired arcs in the literal source hierarchy. The representative
phases are properties of their actual physical endpoints. -/
structure Data {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1)
    (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1)
    (address : Address (a+h)) where
  arcFalse : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
    (SourceProfile.clock he C a h S ho false address) (2*u)
  arcTrue : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) h)
    (SourceProfile.clock he C a h S ho true address) (2*u)
  start_equal : arcFalse.vertex ⟨0,by omega⟩=arcTrue.vertex ⟨0,by omega⟩
  end_equal : arcFalse.vertex ⟨2*u,by omega⟩=arcTrue.vertex ⟨2*u,by omega⟩
  false_code : ((SourceProfile.clock he C a h S ho false address).position
    (arcFalse.vertex ⟨0,by omega⟩)).val%(2^(a+h+1))=(DenseSourceMarks.code r hr false address).val
  true_code : ((SourceProfile.clock he C a h S ho true address).position
    (arcTrue.vertex ⟨2*u,by omega⟩)).val%(2^(a+h+1))=(DenseSourceMarks.code r hr true address).val

/-- The record is constructed from the checked uniform paired-source theorem,
not taken as an existence premise. -/
theorem data_exists {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1)
    (address : Address (a+h))
    (hbalance : Profile.prefixCount (S (lowerAddress address)) (2*u)=u) :
    Nonempty (Data (u:=u) he C a h r hr S ho address) := by
  obtain ⟨p,q,hs,he',hc,hc'⟩ := CodePairedArcs.exists_pair he C a h r hr hh room hA S ho address hbalance
  exact ⟨⟨p,q,hs,he',hc,hc'⟩⟩

/-- Select actual paired data for every address, retaining the actual literal
endpoints at all later uses. -/
noncomputable def family {V : Type} {e u : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool)
    (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
    (address : Address (a+h)) : Data (u:=u) he C a h r hr S ho address :=
  Classical.choice (data_exists he C a h r hr hh room hA S ho address (hbalance address))

/-- False factors use the actual arc start; true factors use the actual arc
end. These full scalar positions may differ from canonical code indices. -/
noncomputable def endpoint {V : Type} {e u a h r : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hr : r<a+h+1} {S : Address a→Fin (2^(e*2^a))→Bool}
    {ho : ∀address, Profile.cardinality (S address)%2=1} {address : Address (a+h)}
    (D : Data (u:=u) he C a h r hr S ho address) (epsilon : Bool) :
    Fin (lengthPower ((2^(e*2^a))*(2^(e*2^a))) h) :=
  if epsilon then (SourceProfile.clock he C a h S ho true address).position
    (D.arcTrue.vertex ⟨2*u,by omega⟩) else
    (SourceProfile.clock he C a h S ho false address).position (D.arcFalse.vertex ⟨0,by omega⟩)

theorem endpoint_code {V : Type} {e u a h r : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hr : r<a+h+1} {S : Address a→Fin (2^(e*2^a))→Bool}
    {ho : ∀address, Profile.cardinality (S address)%2=1} {address : Address (a+h)}
    (D : Data (u:=u) he C a h r hr S ho address) (epsilon : Bool) :
    (endpoint D epsilon).val%(2^(a+h+1))=(DenseSourceMarks.code r hr epsilon address).val := by
  cases epsilon
  · exact D.false_code
  · exact D.true_code

/-- The chosen index is an inverse coordinate of the actual physical
endpoint; it is never replaced by the canonical integer representative. -/
theorem endpoint_vertex {V : Type} {e u a h r : Nat} {he : 2≤e} {C : ClockData V (2^e)}
    {hr : r<a+h+1} {S : Address a→Fin (2^(e*2^a))→Bool}
    {ho : ∀address, Profile.cardinality (S address)%2=1} {address : Address (a+h)}
    (D : Data (u:=u) he C a h r hr S ho address) (epsilon : Bool) :
    (SourceProfile.clock he C a h S ho epsilon address).cycle (endpoint D epsilon)=
      if epsilon then D.arcTrue.vertex ⟨2*u,by omega⟩ else D.arcFalse.vertex ⟨0,by omega⟩ := by
  cases epsilon <;> simp only [endpoint,Bool.false_eq_true,ite_false,ite_true]
  · exact (SourceProfile.clock he C a h S ho false address).cycle_position _
  · exact (SourceProfile.clock he C a h S ho true address).cycle_position _

/-- Canonical literal oriented source clock, anchored at the selected actual
paired endpoint and transported only by the proved complete length equality. -/
noncomputable def orientedSource {V : Type} {e u : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
    (epsilon : Bool) (address : Address (a+h)) (z : Fin (2^r)) :
    ClockData (VertexPower (VertexPower V a×VertexPower V a) h)
      (2^(e*2^(a+h+1)-r)*2^r) :=
  let hK := Nat.two_pow_pos (e*2^(a+h+1)-r)
  let D := family he C a h r hr hh room hA S ho hbalance address
  let raw := castClock (SourceLengths.fine_length he a h r hr)
    (SourceProfile.clock he C a h S ho epsilon address)
  OrientedClock.clock (Nat.mul_pos hK (Nat.two_pow_pos r)) raw
    (OrientedClock.index (Nat.mul_pos hK (Nat.two_pow_pos r))
      (Fin.cast (SourceLengths.fine_length he a h r hr) (endpoint D epsilon))
      (!epsilon) (BaselinePhysical.threshold hK z)) epsilon

/-- Complete instantiation of baseline source mark classes at constructed
physical endpoints, with the former hcode premise removed. -/
theorem anti_classes {V : Type} {e u K B L b : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
    (hK : 0<K) (hL : 0<L) (hd : 2*L∣K) (hb : b<L) (heven : L%2=0) (hodd : b%2=1)
    (hlen : lengthPower ((2^(e*2^a))*(2^(e*2^a))) h=K*2^r)
    (hperiod : 2^r*L=2^(a+h+1)) (epsilon : Bool) (address : Address (a+h))
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) (j : Fin B) :
    let D := family he C a h r hr hh room hA S ho hbalance address
    let raw := castClock hlen (SourceProfile.clock he C a h S ho epsilon address)
    let G := OrientedClock.clock (Nat.mul_pos hK (Nat.two_pow_pos r)) raw
      (OrientedClock.index (Nat.mul_pos hK (Nat.two_pow_pos r))
        (Fin.cast hlen (endpoint D epsilon)) (!epsilon) (BaselinePhysical.threshold hK z)) epsilon
    AACMarkIntervals.IsMark hK
      (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) w.1) z (G.position v,j) ↔
      ∃i : Fin b, DenseSourceMarks.Marked he C a h r hr S ho (fun eps _=>!eps)
        epsilon address i.val v := by
  dsimp only
  exact SourcePhysicalMarks.anti_source_classes he C a h r hr S ho hK hL hd hb heven hodd
    hlen hperiod epsilon address _ (endpoint_code _ epsilon) z v j

/-- Canonical coarse/block sizes discharge all source length and anti-period
transport premises. Only the genuine pattern/profile inputs remain. -/
theorem canonical_classes {V : Type} {e u B b : Nat}
    (he : 2≤e) (C : ClockData V (2^e)) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
    (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
    (S : Address a→Fin (2^(e*2^a))→Bool) (ho : ∀address, Profile.cardinality (S address)%2=1)
    (hbalance : ∀address : Address (a+h), Profile.prefixCount (S (lowerAddress address)) (2*u)=u)
    (hb : b<2^(a+h+1-r)) (hodd : b%2=1) (epsilon : Bool) (address : Address (a+h))
    (z : Fin (2^r)) (v : VertexPower (VertexPower V a×VertexPower V a) h) (j : Fin B) :
    let hK := Nat.two_pow_pos (e*2^(a+h+1)-r)
    let G := orientedSource he C a h r hr hh room hA S ho hbalance epsilon address z
    AACMarkIntervals.IsMark hK
      (fun w=>TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
        (TurnPatterns.anti (L:=2^(a+h+1-r)) b) w.1) z (G.position v,j) ↔
      ∃i : Fin b, DenseSourceMarks.Marked he C a h r hr S ho (fun eps _=>!eps)
        epsilon address i.val v := by
  dsimp only [orientedSource]
  exact anti_classes he C a h r hr hh room hA S ho hbalance (Nat.two_pow_pos _)
    (Nat.two_pow_pos _) (SourceLengths.coarse_period he a h r hr) hb
    (SourceLengths.block_even a h r hr) hodd (SourceLengths.fine_length he a h r hr)
    (SourceLengths.code_period a h r hr) epsilon address z v j

#print axioms canonical_classes
#print axioms data_exists
#print axioms endpoint_code
#print axioms anti_classes
end ErdePaths.SourceCodeOrigins
