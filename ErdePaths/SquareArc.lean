import ErdePaths.PhaseArc

namespace ErdePaths.SquareArc
open SourceClock SquareLift

theorem pair_step {N : Nat} (hN : 0<N) (a r : Fin N) (hr : r.val+1<N) :
    pairIndex (a,⟨r.val+1,hr⟩)=successor (Nat.mul_pos hN hN) (pairIndex (a,r)) := by
  apply Fin.ext
  have hb := (pairIndex (a,⟨r.val+1,hr⟩)).isLt
  change N*a.val+(r.val+1)=(N*a.val+r.val+1)%(N*N)
  have hb' : N*a.val+r.val+1<N*N := by
    change N*a.val+(r.val+1)<N*N at hb
    omega
  rw [Nat.mod_eq_of_lt hb']
  omega

/-- The actual minus clock follows a parent forward edge in the first
coordinate unless that edge is the omitted connector at the fixed vertex. -/
theorem minus_step {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (u v w : V) (hv : C.position v=successor hN (C.position u)) (hw : w≠v) :
    minusClock hN C (v,w)=successor (Nat.mul_pos hN hN) (minusClock hN C (u,w)) := by
  let g := C.position w
  let r := backward hN (C.position u) g
  have hx : forward hN g r=C.position u := forward_inverse hN g (C.position u)
  have hr : r.val+1<N := by
    by_cases h : r.val+1<N
    · exact h
    · have hl : r.val=N-1 := by have := r.isLt; omega
      have he : r=⟨N-1,by omega⟩ := Fin.ext hl
      rw [he,forward_last] at hx
      have hs : C.position v=g := by rw [hv,←hx,successor_predecessor]
      exact False.elim (hw (by
        have hh := congrArg C.cycle hs
        simpa only [g,C.cycle_position] using hh.symm))
  have hy : backward hN (C.position v) g=⟨r.val+1,hr⟩ := by
    apply forward_injective hN g
    rw [forward_inverse,←successor_forward_step hN g hr,hx,hv]
  change pairIndex (negate hN g,backward hN (C.position v) g)=
    successor (Nat.mul_pos hN hN) (pairIndex (negate hN g,r))
  rw [hy]
  exact pair_step hN _ r hr

/-- The actual plus clock follows the same parent edge backwards in its
second coordinate, with the literal omitted connector excluded. -/
theorem plus_step {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N)
    (u v w : V) (hv : C.position v=successor hN (C.position u)) (hw : w≠u) :
    plusClock hN C (w,u)=successor (Nat.mul_pos hN hN) (plusClock hN C (w,v)) := by
  let g := C.position w
  let r := backward hN g (C.position v)
  have hy : backward hN g r=C.position v := backward_inverse hN g (C.position v)
  have hr : r.val+1<N := by
    by_cases h : r.val+1<N
    · exact h
    · have hl : r.val=N-1 := by have := r.isLt; omega
      have he : r=⟨N-1,by omega⟩ := Fin.ext hl
      rw [he,backward_last] at hy
      have hs : C.position u=g := by
        have hh : successor hN (C.position u)=successor hN g := hv.symm.trans hy.symm
        have hh' := congrArg (predecessor hN) hh
        simpa only [predecessor_successor] using hh'
      exact False.elim (hw (by
        have hh := congrArg C.cycle hs
        simpa only [g,C.cycle_position] using hh.symm))
  have hx : backward hN g ⟨r.val+1,hr⟩=C.position u := by
    have hs : successor hN (backward hN g ⟨r.val+1,hr⟩)=successor hN (C.position u) := by
      rw [successor_backward_step hN g hr,hy,hv]
    have hs' := congrArg (predecessor hN) hs
    simpa only [predecessor_successor] using hs'
  have hr' : backward hN g (C.position u)=⟨r.val+1,hr⟩ := by
    rw [←hx,backward_inverse]
  change pairIndex (g,backward hN g (C.position u))=
    successor (Nat.mul_pos hN hN) (pairIndex (g,r))
  rw [hr']
  exact pair_step hN _ r hr

#print axioms plus_step
#print axioms minus_step
end ErdePaths.SquareArc
