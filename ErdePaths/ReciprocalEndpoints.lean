import ErdePaths.ReciprocalIncidence
import ErdePaths.PairedArc
import ErdePaths.OrientedClock

namespace ErdePaths.ReciprocalEndpoints
open SquareLift SourceClock PairedArc AnchoredEmbedding AACTransition AACMarkExchange

private theorem add_comm {N} (hN : 0<N) (i j : Fin N) : forward hN i j=forward hN j i := by
  apply Fin.ext; simp [forward,Nat.add_comm]

private theorem add_assoc {N} (hN : 0<N) (i j k : Fin N) :
    forward hN (forward hN i j) k=forward hN i (forward hN j k) := by
  apply Fin.ext
  simp only [forward,Nat.mod_add_mod,Nat.add_mod_mod,Nat.add_assoc]

/-- Actual arc endpoints, retaining the complete position modulo the full cycle. -/
theorem arc_end {V N A} (hN : 0<N) (C : ClockData V N) (p : DirectedArc hN C A) (ha : A<N) :
    C.position (p.vertex ⟨A,by omega⟩)=forward hN (C.position (p.vertex ⟨0,by omega⟩)) ⟨A,ha⟩ := by
  apply Fin.ext
  have hh := phase_consecutive hN C p (show N∣N from Nat.dvd_refl N) (⟨A,by omega⟩ : Fin (A+1))
  simpa only [Nat.mod_eq_of_lt (C.position _).isLt,forward] using hh

/-- Forward origin places the arc END at threshold z; predecessor threshold
then lands at its START. Reverse origin places START at z and END at predecessor. -/
def forwardClock {V N A} (hN : 0<N) (C : ClockData V N) (p : DirectedArc hN C A)
    (z : Fin N) : ClockData V N :=
  OrientedClock.clock hN C (backward hN (C.position (p.vertex ⟨A,by omega⟩)) z) true

def reverseClock {V N A} (hN : 0<N) (C : ClockData V N) (p : DirectedArc hN C A)
    (z : Fin N) : ClockData V N :=
  OrientedClock.clock hN C (forward hN (C.position (p.vertex ⟨0,by omega⟩)) z) false

theorem forward_at_threshold {V N A} (hN : 0<N) (C : ClockData V N)
    (p : DirectedArc hN C A) (z : Fin N) :
    (forwardClock hN C p z).cycle z=p.vertex ⟨A,by omega⟩ := by
  change C.cycle (forward hN (backward hN (C.position (p.vertex ⟨A,by omega⟩)) z) z)=_
  rw [add_comm,forward_inverse,C.cycle_position]

theorem reverse_at_threshold {V N A} (hN : 0<N) (C : ClockData V N)
    (p : DirectedArc hN C A) (z : Fin N) :
    (reverseClock hN C p z).cycle z=p.vertex ⟨0,by omega⟩ := by
  change C.cycle (backward hN (forward hN (C.position (p.vertex ⟨0,by omega⟩)) z) z)=_
  rw [add_comm hN (C.position (p.vertex ⟨0,by omega⟩)) z,HamiltonNormalize.unrotate_rotate,C.cycle_position]

theorem forward_at_previous {V N A} (hN : 0<N) (C : ClockData V N)
    (p : DirectedArc hN C A) (ha : A<N) (z t : Fin N)
    (ht : forward hN t ⟨A,ha⟩=z) :
    (forwardClock hN C p z).cycle t=p.vertex ⟨0,by omega⟩ := by
  change C.cycle (forward hN (backward hN (C.position (p.vertex ⟨A,by omega⟩)) z) t)=_
  have he : forward hN (backward hN (C.position (p.vertex ⟨A,by omega⟩)) z) t=C.position (p.vertex ⟨0,by omega⟩) := by
    apply forward_injective hN ⟨A,ha⟩
    rw [add_comm hN ⟨A,ha⟩,add_assoc,ht,add_comm,forward_inverse]
    exact (arc_end hN C p ha).trans (add_comm _ _ _)
  rw [he,C.cycle_position]

theorem reverse_at_previous {V N A} (hN : 0<N) (C : ClockData V N)
    (p : DirectedArc hN C A) (ha : A<N) (z t : Fin N)
    (ht : forward hN t ⟨A,ha⟩=z) :
    (reverseClock hN C p z).cycle t=p.vertex ⟨A,by omega⟩ := by
  change C.cycle (backward hN (forward hN (C.position (p.vertex ⟨0,by omega⟩)) z) t)=_
  have he : backward hN (forward hN (C.position (p.vertex ⟨0,by omega⟩)) z) t=C.position (p.vertex ⟨A,by omega⟩) := by
    apply forward_injective hN t
    rw [forward_inverse,arc_end hN C p ha,add_comm hN t,add_assoc,add_comm hN ⟨A,ha⟩,ht]
  rw [he,C.cycle_position]

theorem threshold_previous {K A : Nat} (hK : 1<K) (hA : 0<A) (z : Fin A) :
    forward (Nat.mul_pos (by omega) hA)
      (positionEncode (predecessor (by omega) (⟨0,by omega⟩ : Fin K)) z)
      ⟨A,by have hh := Nat.mul_lt_mul_of_pos_right hK hA; simpa using hh⟩=
    positionEncode (⟨0,by omega⟩ : Fin K) z := by
  apply Fin.ext
  simp only [forward,positionEncode,predecessor,Nat.add_zero]
  rw [Nat.mod_eq_of_lt (show K-1<K by omega)]
  have he : (K-1)*A+A=K*A := by
    rw [←Nat.succ_mul]
    congr 1; omega
  have hs : (K-1)*A+z.val+A=K*A+z.val := by omega
  rw [Nat.mul_comm A (K-1),Nat.mul_zero,hs,Nat.add_mod,Nat.mod_self,Nat.zero_add,Nat.mod_mod]
  simp only [Nat.zero_add]
  have hl : A<K*A := by have hh := Nat.mul_lt_mul_of_pos_right hK hA; simpa using hh
  exact Nat.mod_eq_of_lt (Nat.lt_trans z.isLt hl)

/-- Actual host embedding from two literal cycle clocks. -/
def host {V W K A B} (F : ClockData V (K*A)) (H : ClockData W B) : Fine K A B→V×W :=
  fun v => (F.cycle v.1,H.cycle v.2)

theorem host_injective {V W K A B} (F : ClockData V (K*A)) (H : ClockData W B) :
    Function.Injective (host F H) := by
  intro x y he
  have hx := congrArg (fun v : V×W => F.position v.1) he
  have hy := congrArg (fun v : V×W => H.position v.2) he
  simp only [host,F.position_cycle,H.position_cycle] at hx hy
  exact Prod.ext hx hy

/-- All rows except the literal last row enumerate exactly H minus h*. -/
theorem rows_except_last {W B} (hB : 0<B) (H : ClockData W B) (w : W) :
    (∃j : Fin B, j.val<B-1 ∧ H.cycle j=w) ↔ w≠H.cycle ⟨B-1,by omega⟩ := by
  constructor
  · rintro ⟨j,hj,hw⟩ he
    have hp := congrArg H.position (hw.trans he)
    simp only [H.position_cycle] at hp
    have hv := congrArg Fin.val hp
    change j.val=B-1 at hv
    omega
  · intro hw
    refine ⟨H.position w,?_,H.cycle_position w⟩
    have hh := (H.position w).isLt
    apply Classical.byContradiction
    intro hn
    have he : H.position w=⟨B-1,by omega⟩ := by
      apply Fin.ext
      change (H.position w).val=B-1
      omega
    apply hw
    rw [←he,H.cycle_position]

private theorem removed_image {V W K A B} (hK : 0<K) (hB : 0<B)
    (F : ClockData V (K*A)) (H : ClockData W B) (z : Fin A) (v : V×W) :
    ImageSet (host F H) (Removed hK (B-1) z) v ↔
      v.1=F.cycle (positionEncode ⟨0,hK⟩ z) ∧ v.2≠H.cycle ⟨B-1,by omega⟩ := by
  constructor
  · rintro ⟨x,hx,j,hj,hpoint⟩
    subst x
    have he := Prod.mk.inj hx
    exact ⟨he.1.symm,(rows_except_last hB H v.2).mp ⟨j,hj,he.2⟩⟩
  · rintro ⟨hv,hw⟩
    obtain ⟨j,hj,he⟩ := (rows_except_last hB H v.2).mpr hw
    exact ⟨(positionEncode ⟨0,hK⟩ z,j),Prod.ext hv.symm he,j,hj,rfl⟩

private theorem added_image {V W K A B} (hK : 0<K) (hB : 0<B)
    (F : ClockData V (K*A)) (H : ClockData W B) (z : Fin A) (v : V×W) :
    ImageSet (host F H) (Added hK (B-1) z) v ↔
      v.1=F.cycle (positionEncode (predecessor hK ⟨0,hK⟩) z) ∧ v.2≠H.cycle ⟨B-1,by omega⟩ := by
  constructor
  · rintro ⟨x,hx,j,hj,hpoint⟩
    subst x
    have he := Prod.mk.inj hx
    exact ⟨he.1.symm,(rows_except_last hB H v.2).mp ⟨j,hj,he.2⟩⟩
  · rintro ⟨hv,hw⟩
    obtain ⟨j,hj,he⟩ := (rows_except_last hB H v.2).mpr hw
    exact ⟨(positionEncode (predecessor hK ⟨0,hK⟩) z,j),Prod.ext hv.symm he,j,hj,rfl⟩

/-- Actual endpoint image exchange, allowing different H tours and row order.
The paired arcs supply physical common endpoints; the shared last H vertex
supplies the same omitted physical row. -/
theorem image_exchanges {V W K A B} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (C D : ClockData V (K*A))
    (p : DirectedArc (Nat.mul_pos (by omega) hA) C A)
    (q : DirectedArc (Nat.mul_pos (by omega) hA) D A)
    (hstart : p.vertex ⟨0,by omega⟩=q.vertex ⟨0,by omega⟩)
    (hend : p.vertex ⟨A,by omega⟩=q.vertex ⟨A,by omega⟩)
    (H J : ClockData W B)
    (hlast : H.cycle ⟨B-1,by omega⟩=J.cycle ⟨B-1,by omega⟩) (z : Fin A) :
    let F := forwardClock (Nat.mul_pos (by omega) hA) C p (positionEncode (⟨0,by omega⟩ : Fin K) z)
    let G := reverseClock (Nat.mul_pos (by omega) hA) D q (positionEncode (⟨0,by omega⟩ : Fin K) z)
    (∀v : V×W, ImageSet (host F H) (Removed (by omega) (B-1) z) v ↔
      ImageSet (host G J) (Added (by omega) (B-1) z) v) ∧
    (∀v : V×W, ImageSet (host G J) (Removed (by omega) (B-1) z) v ↔
      ImageSet (host F H) (Added (by omega) (B-1) z) v) := by
  dsimp only
  have ha : A<K*A := by have hh := Nat.mul_lt_mul_of_pos_right hK hA; simpa using hh
  constructor
  · intro v
    rw [removed_image (by omega) hB,added_image (by omega) hB,
      forward_at_threshold,reverse_at_previous _ _ _ ha _ _ (threshold_previous hK hA z),hend,hlast]
  · intro v
    rw [removed_image (by omega) hB,added_image (by omega) hB,
      reverse_at_threshold,forward_at_previous _ _ _ ha _ _ (threshold_previous hK hA z),hstart,hlast]

/-- Actual paired-arc construction preserves pointwise physical mark count
through the all-but-last merge, without assumed endpoint-set equality. -/
theorem preservation {V W K A B} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (C D : ClockData V (K*A))
    (p : DirectedArc (Nat.mul_pos (by omega) hA) C A)
    (q : DirectedArc (Nat.mul_pos (by omega) hA) D A)
    (hstart : p.vertex ⟨0,by omega⟩=q.vertex ⟨0,by omega⟩)
    (hend : p.vertex ⟨A,by omega⟩=q.vertex ⟨A,by omega⟩)
    (H J : ClockData W B)
    (hlast : H.cycle ⟨B-1,by omega⟩=J.cycle ⟨B-1,by omega⟩) (z : Fin A)
    (t t' : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (ht0' : t' ⟨0,by omega⟩=false) (ht1' : t' ⟨1,hK⟩=false)
    (htlast' : t' (predecessor (by omega) ⟨0,by omega⟩)=true) (v : V×W) :
    let F := forwardClock (Nat.mul_pos (by omega) hA) C p (positionEncode (⟨0,by omega⟩ : Fin K) z)
    let G := reverseClock (Nat.mul_pos (by omega) hA) D q (positionEncode (⟨0,by omega⟩ : Fin K) z)
    incidence (ImageSet (host F H) (AACMarkIntervals.IsMark (by omega) (AACInduction.turnsAfter (by omega) t (B-1)) z) v)+
      incidence (ImageSet (host G J) (AACMarkIntervals.IsMark (by omega) (AACInduction.turnsAfter (by omega) t' (B-1)) z) v)=
    incidence (ImageSet (host F H) (AACMarkIntervals.IsMark (by omega) (fun w => t w.1) z) v)+
      incidence (ImageSet (host G J) (AACMarkIntervals.IsMark (by omega) (fun w => t' w.1) z) v) := by
  dsimp only
  have he := image_exchanges hK hA hB C D p q hstart hend H J hlast z
  exact ReciprocalIncidence.preservation hK t t' ht0 ht1 htlast ht0' ht1' htlast'
    (B-1) z _ _ (host_injective _ _) (host_injective _ _) he.1 he.2 v

#print axioms arc_end
#print axioms image_exchanges
#print axioms preservation
end ErdePaths.ReciprocalEndpoints
