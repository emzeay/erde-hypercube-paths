import ErdePaths.MersenneOrientedFactors
import ErdePaths.SourceChronologicalMarks
import ErdePaths.ZeroUpperFactors

namespace ErdePaths.ZeroUpperChronologicalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts SquareLift
open AACTransition AACFine AACFineClock AACMarkIntervals
attribute [local instance] Classical.propDecidable

private theorem exponent_room (t : Nat) : t+1≤2^t := by
  induction t with
  | zero => decide
  | succ t ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos t; omega
private theorem coarse_div {e : Nat} (he : 2≤e) (k h : Nat) :
    2*2^(k+h+1)∣2^(e*2^(k+h+1)-1) := by
  have hp := exponent_room (k+h+1)
  have hm := Nat.mul_le_mul_right (2^(k+h+1)) he
  have hd : k+h+2≤e*2^(k+h+1)-1 := by omega
  simpa only [Nat.pow_succ,Nat.mul_comm] using Nat.pow_dvd_pow 2 hd

noncomputable def sourceEuler {e B : Nat} (he : 2≤e) (k h : Nat) (hk : 2≤k) (hB : 0<B) :
    SourceChronologicalMarks.EulerData (Nat.two_pow_pos (e*2^(k+h+1)-1)) (by decide : 0<2) hB
      (TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) (TurnPatterns.long (P:=2^(k+h+1)))) :=
  SourceChronologicalMarks.euler _ _ hB _
    (TurnPatterns.repeated_long_balanced
      (Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)) (coarse_div he k h))
    ((TurnPatterns.repeated_zero _ _ _).trans
      (TurnPatterns.long_zero (Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega))))

section Source
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Address k→Fin (2^(e*2^k))→Bool) (ho : ∀a, Profile.cardinality (S a)%2=1)
  (exceptional : Bool)
  (origins : ∀a : Address (k+h), MersenneCodeOrigins.Data he C k h (by omega) S ho exceptional a) (z : Fin 2)
local notation "K" => 2^(e*2^(k+h+1)-1)

noncomputable def word (hB : 0<B) (H : Bool→Address (k+h)→ClockData W B)
    (q : Vertex (k+h+1)) : List (VertexPower (VertexPower V k×VertexPower V k) h×W) :=
  let E := sourceEuler he k h hk hB
  (markWord (Nat.two_pow_pos _) (by decide) hB E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) z).map
    (AACFineGeometry.physical
      (ZeroUpperIncidence.Geometric.orientedSource he C k h hk room S ho exceptional origins
        (epsilonOf 1 q) (addressOf 1 q) z) (H (epsilonOf 1 q) (addressOf 1 q)))

/-- The chronological word incidence is exactly the actual postflip mark
image indicator; no word count or completeness premise is supplied. -/
theorem word_incidence (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0) (hz : 0<z.val)
    (H : Bool→Address (k+h)→ClockData W B) (q : Vertex (k+h+1))
    (v : VertexPower (VertexPower V k×VertexPower V k) h×W) :
    (word he C k h hk room S ho exceptional origins z hB H q).countP (fun w=>decide (w=v))=
      AACMarkExchange.incidence (ZeroUpperIncidence.Reciprocal.markSet he C k h hk room S ho exceptional origins H true (epsilonOf 1 q) (addressOf 1 q) z v) := by
  have hK4 := SourceLengths.coarse_size he k h 1 (show 1<k+h+1 by omega)
  have h3 : 3≤K*2 := by omega
  have hE2 : 2≤K*B*(2+1) := by
    have hm := Nat.mul_le_mul_right B hK4
    omega
  let E := sourceEuler he k h hk hB
  have hc := AACMarkWord.physical_word_incidence (Nat.two_pow_pos _) (by decide) hB h3 hB3 hb
    E.orbit E.length (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) hE2
    E.injective E.surjective z hz
    (ZeroUpperIncidence.Geometric.orientedSource he C k h hk room S ho exceptional origins
      (epsilonOf 1 q) (addressOf 1 q) z) (H (epsilonOf 1 q) (addressOf 1 q)) v
  simp only [ZeroUpperIncidence.Reciprocal.markSet,ite_true,AACMarkExchange.incidence,
    SourceMarkMulticover.host_image_iff]
  refine Eq.trans ?_ hc
  apply List.countP_congr
  intro w hw
  simp only [decide_eq_true_eq]

end Source

private theorem long_seams {e : Nat} (he : 2≤e) (k h : Nat) (hk : 2≤k) :
    let K := 2^(e*2^(k+h+1)-1)
    let t : Fin K→Bool := TurnPatterns.repeated (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
      (TurnPatterns.long (P:=2^(k+h+1)))
    t ⟨0,Nat.two_pow_pos _⟩=false ∧
    t ⟨1,by have := SourceLengths.coarse_size he k h 1 (by omega); omega⟩=false ∧
    t (predecessor (Nat.two_pow_pos _) ⟨0,Nat.two_pow_pos _⟩)=true := by
  have hp : 8≤2^(k+h+1) := Nat.pow_le_pow_right (show 1≤2 by decide) (show 3≤k+h+1 by omega)
  dsimp only
  constructor
  · rw [TurnPatterns.repeated_zero]; exact TurnPatterns.long_zero hp
  constructor
  · unfold TurnPatterns.repeated
    have ht : (⟨1%(2*2^(k+h+1)),Nat.mod_lt _ (Nat.mul_pos (by decide) (Nat.two_pow_pos _))⟩ : Fin (2*2^(k+h+1)))=
        ⟨1,by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
    rw [ht]; exact TurnPatterns.long_one hp
  · have hs : predecessor (Nat.two_pow_pos _) (⟨0,Nat.two_pow_pos _⟩ : Fin (2^(e*2^(k+h+1)-1)))=
        ⟨2^(e*2^(k+h+1)-1)-1,by have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega⟩ := by
      apply Fin.ext
      simp [predecessor,Nat.mod_eq_of_lt (show 2^(e*2^(k+h+1)-1)-1<2^(e*2^(k+h+1)-1) by
        have := Nat.two_pow_pos (e*2^(k+h+1)-1); omega)]
    rw [hs,TurnPatterns.repeated_last _ (Nat.two_pow_pos _) (coarse_div he k h)]
    exact TurnPatterns.long_last hp

section Cube
variable {e d m B : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
  (he : 2≤e) (k h : Nat) (hk : 2≤k) (room : 2^(k+h+3)∣lengthPower (2^e) k)
  (S : Fin m→Address k→Fin (2^(e*2^k))→Bool) (ho : ∀f a, Profile.cardinality (S f a)%2=1)
  (exceptional : Bool)
  (origins : ∀f a, MersenneCodeOrigins.Data he (D.cycles f).toClockData k h (by omega) (S f) (ho f) exceptional a) (z : Fin 2)
local notation "K" => 2^(e*2^(k+h+1)-1)

/-- Actual physical parity balance using genuine owned Mersenne source
Hamilton factors. No source adjacency or balanced-word premise. -/
theorem balanced (hB : 0<B) (hB3 : 3≤B) (hbeven : B%2=0) (hz : 0<z.val)
    (H : Bool→Address (k+h)→HamiltonData.CycleData (Vertex d) (@Adjacent d) B hB)
    (f : Fin m) (q : Vertex (k+h+1)) :
    NoncrossingMatch.Balanced (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=k) (h:=h))
      (word he (D.cycles f).toClockData k h hk room (S f) (ho f) exceptional (origins f) z hB
        (fun eps a=>(H eps a).toClockData) q) := by
  let I := CubeHierarchy.sourceIso e k h
  let actual := CubeHierarchy.transport I (ZeroUpperFactors.factors D he k h hk S ho exceptional origins z)
  let F := actual.cycles (SourceFactors.index k h f (epsilonOf 1 q) (addressOf 1 q))
  let G := ZeroUpperIncidence.Geometric.orientedSource he (D.cycles f).toClockData k h hk room
    (S f) (ho f) exceptional (origins f) (epsilonOf 1 q) (addressOf 1 q) z
  have hF (i : Fin (K*2)) : F.cycle i=I.encode (G.cycle i) := by
    have hc := ZeroUpperFactors.clock_eq D he k h hk S ho exceptional origins
      z f (epsilonOf 1 q) (addressOf 1 q)
    exact congrArg (fun T : ClockData _ (K*2)=>I.encode (T.cycle i)) hc
  have hK4 := SourceLengths.coarse_size he k h 1 (show 1<k+h+1 by omega)
  have h3 : 3≤K*2 := by omega
  have hE2 : 2≤K*B*(2+1) := by have hm := Nat.mul_le_mul_right B hK4; omega
  have hseam := long_seams he k h hk
  let E := sourceEuler he k h hk hB
  have hc := AACPhysicalBalance.chronological_physical_balanced
    (show 1<K by omega) (by decide) hB h3 hB3 hbeven F (H (epsilonOf 1 q) (addressOf 1 q))
    rfl _ hseam.1 hseam.2.1 hseam.2.2 (B-1) E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) hE2 E.injective E.surjective z hz
  have hw :
      (word he (D.cycles f).toClockData k h hk room (S f) (ho f) exceptional (origins f) z hB
        (fun eps a=>(H eps a).toClockData) q).map (fun v=>CubeProduct.encode (I.encode v.1,v.2))=
      (markWord (Nat.two_pow_pos _) (by decide) hB E.orbit E.length
        (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by decide)) z).map
        (fun v=>CubeProduct.encode (F.cycle v.1,(H (epsilonOf 1 q) (addressOf 1 q)).cycle v.2)) := by
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
end Cube



namespace Actual
section Definitions
variable {V W : Type} {e B : Nat} (he : 2≤e) (C : ClockData V (2^e))
  (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k) (exceptional : Bool)

noncomputable abbrev word (z : Fin 2) (hB : 0<B)
    (H : Bool→Address k→ClockData W B) (q : Vertex (k+1)) :=
  ZeroUpperChronologicalMarks.word he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (ZeroUpperCodeOrigins.data he k hk room exceptional C) z hB H q

theorem word_incidence (z : Fin 2) (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0) (hz : 0<z.val)
    (H : Bool→Address k→ClockData W B) (q : Vertex (k+1))
    (v : (VertexPower V k×VertexPower V k)×W) :
    (word he C k hk room exceptional z hB H q).countP (fun w=>decide (w=v))=
      AACMarkExchange.incidence (ZeroUpperIncidence.Actual.markSet he C k hk room exceptional
        H true (epsilonOf 1 q) (addressOf 1 q) z v) := by
  have hc := ZeroUpperChronologicalMarks.word_incidence he C k 0 hk (by simpa using room)
    (ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (ZeroUpperCodeOrigins.data he k hk room exceptional C) z hB hB3 hb hz H q v
  refine Eq.trans ?_ hc
  apply List.countP_congr
  intro w hw
  simp only [decide_eq_true_eq]
  rfl

end Definitions

theorem small_multiplicity {V W : Type} {B m : Nat} {R : W→W→Prop}
    (C : ClockData V (2^2)) (t : Nat) (room : 2^(t+2+3)∣lengthPower (2^2) (t+2))
    (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0) (HD : HamiltonData.DecompositionData W R m B hB)
    (last : W) (assigned : Bool→Address (t+2)→Fin m) (z : Fin 2) (hz : 0<z.val)
    (v : (VertexPower V (t+2)×VertexPower V (t+2))×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(t+2+1))).map (fun q=>
      (word (by omega) C (t+2) (by omega) room true z hB H q).countP (fun w=>decide (w=v)))).sum=
      2^(t+2)-1 := by
  dsimp only
  have hf := funext (fun q=>word_incidence (by omega) C (t+2) (by omega) room true
    z hB hB3 hb hz (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData) q v)
  rw [hf]
  exact ZeroUpperIncidence.Actual.normalized_small C t room hB HD last assigned z v

theorem large_multiplicity {V W : Type} {e B m : Nat} {R : W→W→Prop}
    (he : 4≤e) (C : ClockData V (2^e)) (k : Nat) (hk : 2≤k)
    (room : 2^(k+3)∣lengthPower (2^e) k)
    (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0) (HD : HamiltonData.DecompositionData W R m B hB)
    (last : W) (assigned : Bool→Address k→Fin m) (z : Fin 2) (hz : 0<z.val)
    (v : (VertexPower V k×VertexPower V k)×W) :
    let H := fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData
    ((List.finRange (2^(k+1))).map (fun q=>
      (word (by omega) C k hk room false z hB H q).countP (fun w=>decide (w=v)))).sum=2^k-1 := by
  dsimp only
  have hf := funext (fun q=>word_incidence (by omega) C k hk room false
    z hB hB3 hb hz (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData) q v)
  rw [hf]
  exact ZeroUpperIncidence.Actual.normalized_large he C k hk room hB HD last assigned z v

section Cube
variable {e d m B : Nat}
  (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
  (he : 2≤e) (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k) (exceptional : Bool)

theorem balanced (z : Fin 2) (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0) (hz : 0<z.val)
    (H : Bool→Address k→HamiltonData.CycleData (Vertex d) (@Adjacent d) B hB)
    (f : Fin m) (q : Vertex (k+1)) :
    NoncrossingMatch.Balanced (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=k) (h:=0))
      (word he (D.cycles f).toClockData k hk room exceptional z hB (fun eps a=>(H eps a).toClockData) q) :=
  ZeroUpperChronologicalMarks.balanced D he k 0 hk (by simpa using room)
    (fun _=>ZeroUpperCodeOrigins.selectors k hk room exceptional)
    (fun _=>ZeroUpperCodeOrigins.odd k hk room exceptional) exceptional
    (fun f=>ZeroUpperCodeOrigins.data he k hk room exceptional (D.cycles f).toClockData)
    z hB hB3 hb hz H f q
end Cube

noncomputable def small_marks {d m M B : Nat}
    (D : HamiltonData.DecompositionData (Vertex 2) (@Adjacent 2) m (2^2) (Nat.two_pow_pos 2))
    (t : Nat) (room : 2^(t+2+3)∣lengthPower (2^2) (t+2))
    (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
    (last : Vertex d) (assigned : Bool→Address (t+2)→Fin M) (z : Fin 2) (hz : 0<z.val) (f : Fin m) :
    ChordGraph.Marks (VertexPower (VertexPower (Vertex 2) (t+2)×VertexPower (Vertex 2) (t+2)) 0×Vertex d)
      (SourceChronologicalMarks.physicalParity (e:=2) (d:=d) (a:=t+2) (h:=0))
      (2^(t+2+1)) (2^(t+2)-1) where
  word := word (by omega) (D.cycles f).toClockData (t+2) (by omega) room true z hB
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData)
  balanced := balanced D (by omega) (t+2) (by omega) room true z hB hB3 hb hz
    (fun eps a=>(HamiltonCommonLast.normalize HD last).cycles (assigned eps a)) f
  multiplicity v := by
    have hc := small_multiplicity (D.cycles f).toClockData t room hB hB3 hb HD last assigned z hz v
    dsimp only at hc
    refine Eq.trans ?_ hc
    congr 1
    apply List.map_congr_left
    intro q hq
    apply List.countP_congr
    intro x hx
    simp only [decide_eq_true_eq]
    rfl

noncomputable def large_marks {e d m M B : Nat}
    (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
    (he : 4≤e) (k : Nat) (hk : 2≤k) (room : 2^(k+3)∣lengthPower (2^e) k)
    (hB : 0<B) (hB3 : 3≤B) (hb : B%2=0)
    (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
    (last : Vertex d) (assigned : Bool→Address k→Fin M) (z : Fin 2) (hz : 0<z.val) (f : Fin m) :
    ChordGraph.Marks (VertexPower (VertexPower (Vertex e) k×VertexPower (Vertex e) k) 0×Vertex d)
      (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=k) (h:=0))
      (2^(k+1)) (2^k-1) where
  word := word (by omega) (D.cycles f).toClockData k hk room false z hB
    (fun eps a=>((HamiltonCommonLast.normalize HD last).cycles (assigned eps a)).toClockData)
  balanced := balanced D (by omega) k hk room false z hB hB3 hb hz
    (fun eps a=>(HamiltonCommonLast.normalize HD last).cycles (assigned eps a)) f
  multiplicity v := by
    have hc := large_multiplicity he (D.cycles f).toClockData k hk room hB hB3 hb HD last assigned z hz v
    dsimp only at hc
    refine Eq.trans ?_ hc
    congr 1
    apply List.map_congr_left
    intro q hq
    apply List.countP_congr
    intro x hx
    simp only [decide_eq_true_eq]
    rfl
end Actual
#print axioms balanced
#print axioms Actual.balanced
#print axioms Actual.small_marks
#print axioms Actual.large_marks
#print axioms Actual.word_incidence
end ErdePaths.ZeroUpperChronologicalMarks
