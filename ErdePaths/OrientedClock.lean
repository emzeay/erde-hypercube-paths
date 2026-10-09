import ErdePaths.HamiltonNormalize

namespace ErdePaths.OrientedClock
open SourceClock SquareLift HamiltonData HamiltonNormalize

/-- Forward for profile twin true, reverse for twin false, at a literal
physical parent-clock origin. -/
def index {N : Nat} (hN : 0<N) (start : Fin N) (epsilon : Bool) (t : Fin N) : Fin N :=
  if epsilon then forward hN start t else backward hN start t

def inverse {N : Nat} (hN : 0<N) (start : Fin N) (epsilon : Bool) (t : Fin N) : Fin N :=
  if epsilon then backward hN t start else backward hN start t

theorem index_inverse {N : Nat} (hN : 0<N) (start : Fin N) (epsilon : Bool) (t : Fin N) :
    index hN start epsilon (inverse hN start epsilon t)=t := by
  cases epsilon <;> simp only [index,inverse,Bool.false_eq_true,↓reduceIte]
  · exact backward_inverse hN start t
  · exact forward_inverse hN start t

theorem inverse_index {N : Nat} (hN : 0<N) (start : Fin N) (epsilon : Bool) (t : Fin N) :
    inverse hN start epsilon (index hN start epsilon t)=t := by
  cases epsilon <;> simp only [index,inverse,Bool.false_eq_true,↓reduceIte]
  · exact backward_inverse hN start t
  · exact unrotate_rotate hN start t

def clock {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (start : Fin N) (epsilon : Bool) :
    ClockData V N where
  cycle t := C.cycle (index hN start epsilon t)
  position v := inverse hN start epsilon (C.position v)
  position_cycle t := by rw [C.position_cycle,inverse_index]
  cycle_position v := by rw [index_inverse,C.cycle_position]

theorem reverse_step {N : Nat} (hN : 0<N) (start t : Fin N) :
    successor hN (backward hN start (successor hN t))=backward hN start t := by
  by_cases ht : t.val+1<N
  · have hs : successor hN t=⟨t.val+1,ht⟩ := Fin.ext (Nat.mod_eq_of_lt ht)
    rw [hs]
    exact successor_backward_step hN start ht
  · have hl : t=⟨N-1,by omega⟩ := Fin.ext (by change t.val=N-1; have := t.isLt; omega)
    rw [hl,backward_last]
    have hz : successor hN (⟨N-1,by omega⟩ : Fin N)=⟨0,hN⟩ := by
      apply Fin.ext
      simp only [successor]
      have hn : N-1+1=N := by omega
      rw [hn,Nat.mod_self]
    rw [hz,backward_zero]

/-- Reorientation preserves genuine actual cycle adjacency at the wrap edge. -/
def cycle {V R N hN} (C : CycleData V R N hN) (hsym : ∀u v, R u v→R v u)
    (start : Fin N) (epsilon : Bool) : CycleData V R N hN where
  toClockData := clock hN C.toClockData start epsilon
  adjacent t := by
    cases epsilon
    · have ha := C.adjacent (backward hN start (successor hN t))
      rw [reverse_step] at ha
      exact hsym _ _ ha
    · have ha := C.adjacent (forward hN start t)
      rw [←forward_successor] at ha
      exact ha

/-- The raw parent residue of a literal reoriented coordinate retains the
complete physical origin and both modular subtraction borrows. -/
theorem raw_phase {V : Type} {N P : Nat} (hN : 0<N) (hd : P∣N)
    (C : ClockData V N) (start : Fin N) (epsilon : Bool) (t : Fin N) :
    (C.position ((clock hN C start epsilon).cycle t)).val%P=
      if epsilon then (start.val+t.val)%P else (N-t.val+start.val)%P := by
  cases epsilon <;> simp only [clock,index,C.position_cycle,Bool.false_eq_true,↓reduceIte,
    forward,backward,Nat.mod_mod_of_dvd _ hd]

/-- Actual inverse positions of physical vertices in the oriented fine
coordinates, with no freely chosen phase coloring. -/
theorem position_phase {V : Type} {N P : Nat} (hN : 0<N) (hd : P∣N)
    (C : ClockData V N) (start : Fin N) (epsilon : Bool) (v : V) :
    ((clock hN C start epsilon).position v).val%P=
      if epsilon then (N-start.val+(C.position v).val)%P
      else (N-(C.position v).val+start.val)%P := by
  cases epsilon <;> simp only [clock,inverse,Bool.false_eq_true,↓reduceIte,
    backward,Nat.mod_mod_of_dvd _ hd]

#print axioms cycle
#print axioms raw_phase
#print axioms position_phase
end ErdePaths.OrientedClock
