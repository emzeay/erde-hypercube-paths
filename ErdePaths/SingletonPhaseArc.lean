import ErdePaths.AACPatternCardinality
import ErdePaths.PairedArcTower

namespace ErdePaths.SingletonPhaseArc
open SquareLift SourceClock Profile PairedArc

def selector {N : Nat} (c : Fin N) : Fin N→Bool := fun h=>decide (h=c)

theorem cardinality_one {N : Nat} (c : Fin N) : cardinality (selector c)=1 := by
  rw [AACPatternCardinality.cardinality_count,List.countP_eq_length_filter]
  have hp : ((List.finRange N).filter (selector c)).Perm [c] := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp)).mpr
    intro h
    simp [selector]
  rw [hp.length_eq]
  rfl

def arc {N : Nat} (h2 : 2≤N) (c : Fin N) (color : Bool) (i : Fin 3) : Profile.Vertex N :=
  if i.val=0 then (⟨0,by omega⟩,c) else if i.val=1 then
    if color then (⟨0,by omega⟩,successor (by omega) c) else (⟨1,by omega⟩,c)
  else (⟨1,by omega⟩,successor (by omega) c)

theorem arc_simple {N : Nat} (h2 : 2≤N) (c : Fin N) (color : Bool) :
    Function.Injective (arc h2 c color) := by
  intro i j he
  have hn := successor_ne (show 0<N by omega) h2 c
  have hm := Ne.symm hn
  have hi : i.val=0 ∨ i.val=1 ∨ i.val=2 := by have := i.isLt; omega
  have hj : j.val=0 ∨ j.val=1 ∨ j.val=2 := by have := j.isLt; omega
  apply Fin.ext
  rcases hi with hi|hi|hi <;> rcases hj with hj|hj|hj <;> cases color <;>
    simp_all [arc,Prod.mk.injEq,Fin.mk.injEq]

private theorem height_zero {N : Nat} (hN : 0<N) (c : Fin N) :
    height hN ((⟨0,hN⟩ : Fin N),c)=c := by
  apply Fin.ext
  change (0+c.val)%N=c.val
  simpa only [Nat.zero_add] using Nat.mod_eq_of_lt c.isLt

private theorem height_one {N : Nat} (h2 : 2≤N) (c : Fin N) :
    height (by omega) ((⟨1,by omega⟩ : Fin N),c)=successor (by omega) c := by
  apply Fin.ext
  simp only [height,forward,successor]
  rw [Nat.add_comm]

/-- At any literal phase, both positive profile twins share a real two-edge
segment's endpoints. No upper lift or prescribed endpoint existence is needed. -/
theorem arc_step {N : Nat} (h2 : 2≤N) (c : Fin N) (color : Bool) (i : Fin 2) :
    arc h2 c color i.succ=step (by omega) (selector c) color (arc h2 c color i.castSucc) := by
  have hn := successor_ne (show 0<N by omega) h2 c
  have hi : i.val=0 ∨ i.val=1 := by have := i.isLt; omega
  have hz : successor (show 0<N by omega) (⟨0,by omega⟩ : Fin N)=⟨1,by omega⟩ := by
    apply Fin.ext
    change (0+1)%N=1
    exact Nat.mod_eq_of_lt (by omega)
  rcases hi with hi|hi <;> cases color <;>
    simp [arc,hi,step,selector,height_zero,height_one h2 c,hn,hz]

/-- The inverse of the actual profile cycle advances along its real step. -/
theorem clock_step {e : Nat} (he : 1≤e) (S : Fin (2^e)→Bool)
    (ho : cardinality S%2=1) (color : Bool) (v : Profile.Vertex (2^e)) :
    (profileClockData he S ho color).position (step (Nat.two_pow_pos e) S color v)=
      successor (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
        ((profileClockData he S ho color).position v) := by
  let C := profileClockData he S ho color
  have hh := profileCycles_next (Nat.two_pow_pos e) S color (C.position v)
  change C.cycle (successor (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (C.position v))=
    step (Nat.two_pow_pos e) S color (C.cycle (C.position v)) at hh
  rw [C.cycle_position] at hh
  have hp := congrArg C.position hh
  rw [C.position_cycle] at hp
  exact hp.symm

noncomputable def directed {e : Nat} (he : 1≤e) (c : Fin (2^e)) (color : Bool) :
    DirectedArc (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
      (profileClockData he (selector c) (by rw [cardinality_one]) color) 2 where
  vertex:=arc (Nat.pow_le_pow_right (by decide : 1≤2) he) c color
  injective:=arc_simple _ c color
  step i:=by rw [arc_step]; exact clock_step he _ _ color _

theorem start {e : Nat} (he : 1≤e) (c : Fin (2^e)) (color : Bool) :
    (directed he c color).vertex ⟨0,by decide⟩=(⟨0,Nat.two_pow_pos e⟩,c) := rfl

theorem endpoint {e : Nat} (he : 1≤e) (c : Fin (2^e)) (color : Bool) :
    (directed he c color).vertex ⟨2,by decide⟩=
      (⟨1,by have := Nat.pow_le_pow_right (by decide : 1≤2) he; omega⟩,successor (Nat.two_pow_pos e) c) := rfl

/-- Both twins have the exact prescribed modular start phase and endpoint
phase, uniformly at every parent size and even across phase wrap. -/
theorem phases {e D : Nat} (he : 1≤e) (hD : D∣2^e) (c : Fin (2^e)) (color : Bool) :
    ((profileClockData he (selector c) (by rw [cardinality_one]) color).position
      ((directed he c color).vertex ⟨0,by decide⟩)).val%D=c.val%D ∧
    ((profileClockData he (selector c) (by rw [cardinality_one]) color).position
      ((directed he c color).vertex ⟨2,by decide⟩)).val%D=(c.val+2)%D := by
  have hs : ((profileClockData he (selector c) (by rw [cardinality_one]) color).position
      ((directed he c color).vertex ⟨0,by decide⟩)).val%D=c.val%D := by
    rw [start,Profile.profileClock_mod he hD]
    simp
  refine ⟨hs,?_⟩
  have hp := PairedArc.phase_consecutive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) _
    (directed he c color) (Nat.dvd_trans hD (Nat.dvd_mul_right _ _)) (⟨2,by decide⟩ : Fin 3)
  rw [Nat.add_mod,hs] at hp
  exact hp.trans (by simp only [Nat.add_mod,Nat.mod_mod])

/-- Literal transport through any actual parent clock. -/
noncomputable def lifted {V : Type} {e : Nat} (he : 1≤e) (C : ClockData V (2^e))
    (c : Fin (2^e)) (color : Bool) :
    DirectedArc (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
      (ProfileLift.clock he C (selector c) (by rw [cardinality_one]) color) 2 where
  vertex i:=ProfileLift.map C ((directed he c color).vertex i)
  injective:=fun i j hh=>(directed he c color).injective (ProfileLift.map_injective C hh)
  step i:=by
    simp only [ProfileLift.clock,ProfileLift.unmap_map]
    exact (directed he c color).step i

theorem lifted_start {V : Type} {e : Nat} (he : 1≤e) (C : ClockData V (2^e))
    (c : Fin (2^e)) (color : Bool) :
    (lifted he C c color).vertex ⟨0,by decide⟩=(C.cycle ⟨0,Nat.two_pow_pos e⟩,C.cycle c) := rfl

theorem lifted_endpoint {V : Type} {e : Nat} (he : 1≤e) (C : ClockData V (2^e))
    (c : Fin (2^e)) (color : Bool) :
    (lifted he C c color).vertex ⟨2,by decide⟩=
      (C.cycle ⟨1,by have := Nat.pow_le_pow_right (by decide : 1≤2) he; omega⟩,
       C.cycle (successor (Nat.two_pow_pos e) c)) := rfl

theorem lifted_phases {V : Type} {e D : Nat} (he : 1≤e) (hD : D∣2^e)
    (C : ClockData V (2^e)) (c : Fin (2^e)) (color : Bool) :
    ((ProfileLift.clock he C (selector c) (by rw [cardinality_one]) color).position
      ((lifted he C c color).vertex ⟨0,by decide⟩)).val%D=c.val%D ∧
    ((ProfileLift.clock he C (selector c) (by rw [cardinality_one]) color).position
      ((lifted he C c color).vertex ⟨2,by decide⟩)).val%D=(c.val+2)%D := by
  simp only [lifted,ProfileLift.clock,ProfileLift.unmap_map]
  exact phases he hD c color

#print axioms lifted
#print axioms lifted_phases
#print axioms directed
#print axioms phases
end ErdePaths.SingletonPhaseArc
