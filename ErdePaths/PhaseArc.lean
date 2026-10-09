import ErdePaths.SourceClock

namespace ErdePaths.PhaseArc
open SourceClock SquareLift

/-- Literal phase-fiber candidates in an actual Hamilton clock. -/
def candidate {V : Type} {N D : Nat} (C : ClockData V N) (hsize : 3*D≤N)
    (c : Fin D) (q : Fin 3) : V := C.cycle ⟨D*q.val+c.val,by
      have hq : q.val+1≤3 := by have := q.isLt; omega
      have hm := Nat.mul_le_mul_left D hq
      rw [Nat.mul_add,Nat.mul_one] at hm
      have := c.isLt
      omega⟩

theorem candidate_injective {V : Type} {N D : Nat} (C : ClockData V N) (hsize : 3*D≤N)
    (c : Fin D) : Function.Injective (candidate C hsize c) := by
  intro q q' he
  have hp := congrArg C.position he
  simp only [candidate,C.position_cycle] at hp
  have hh := congrArg Fin.val hp
  change D*q.val+c.val=D*q'.val+c.val at hh
  apply Fin.ext
  have hd : 0<D := by have := c.isLt; omega
  apply Nat.eq_of_mul_eq_mul_left hd
  omega

theorem candidate_phase {V : Type} {N D : Nat} (C : ClockData V N) (hsize : 3*D≤N)
    (c : Fin D) (q : Fin 3) : (C.position (candidate C hsize c q)).val%D=c.val := by
  simp only [candidate,C.position_cycle,Nat.mul_add_mod,Nat.mod_eq_of_lt c.isLt]

/-- On an actual consecutive A-edge arc, A<D makes the phase injective,
even when the parent arc crosses its cyclic seam. -/
theorem arc_phase_injective {V : Type} {N D A : Nat} (hD : 0<D) (hA : A<D)
    (C : ClockData V N) (p : Fin (A+1)→V) (start : Nat)
    (hp : ∀i, (C.position (p i)).val%D=(start+i.val)%D) :
    Function.Injective (fun i => (C.position (p i)).val%D) := by
  intro i j he
  have hmod : (start%D+i.val)%D=(start%D+j.val)%D := by
    change (C.position (p i)).val%D=(C.position (p j)).val%D at he
    rw [hp i,hp j] at he
    simpa only [Nat.mod_add_mod] using he
  have hh : forward hD ⟨start%D,Nat.mod_lt _ hD⟩ ⟨i.val,by have := i.isLt; omega⟩=
      forward hD ⟨start%D,Nat.mod_lt _ hD⟩ ⟨j.val,by have := j.isLt; omega⟩ := Fin.ext hmod
  have hh' := forward_injective hD _ hh
  exact Fin.ext (congrArg (fun z : Fin D => z.val) hh')

/-- Each short actual arc excludes at most one candidate in a prescribed
phase fiber, not at most one vertex in the whole parent cycle. -/
theorem arc_forbids_one {V : Type} {N D A : Nat} (hD : 0<D) (hA : A<D)
    (C C' : ClockData V N) (hsize : 3*D≤N) (c : Fin D)
    (hclock : ∀v, (C.position v).val%D=(C'.position v).val%D)
    (p : Fin (A+1)→V) (start : Nat)
    (hp : ∀i, (C'.position (p i)).val%D=(start+i.val)%D)
    (q q' : Fin 3) (i j : Fin (A+1))
    (hi : candidate C hsize c q=p i) (hj : candidate C hsize c q'=p j) : q=q' := by
  have hpi : (C'.position (p i)).val%D=c.val := by
    rw [←hi,←hclock]; exact candidate_phase C hsize c q
  have hpj : (C'.position (p j)).val%D=c.val := by
    rw [←hj,←hclock]; exact candidate_phase C hsize c q'
  have hij := arc_phase_injective hD hA C' p start hp (hpi.trans hpj.symm)
  apply candidate_injective C hsize c
  exact hi.trans ((congrArg p hij).trans hj.symm)

private theorem avoid_two (a b : Fin 3) : ∃q : Fin 3, q≠a ∧ q≠b := by
  have hh : ∀a b : Fin 3, ∃q : Fin 3, q≠a ∧ q≠b := by decide
  exact hh a b

/-- Actual geometric phase prescription: one physical vertex with the
required common phase avoids both complete parent arcs. -/
theorem prescribe_avoiding {V : Type} {N D A : Nat} (hD : 0<D) (hA : A<D)
    (C C' : ClockData V N) (hsize : 3*D≤N) (c : Fin D)
    (hclock : ∀v, (C.position v).val%D=(C'.position v).val%D)
    (p p' : Fin (A+1)→V) (start start' : Nat)
    (hp : ∀i, (C.position (p i)).val%D=(start+i.val)%D)
    (hp' : ∀i, (C'.position (p' i)).val%D=(start'+i.val)%D) :
    ∃w, (C.position w).val%D=c.val ∧ (C'.position w).val%D=c.val ∧
      (∀i, w≠p i) ∧ (∀i, w≠p' i) := by
  classical
  let w := candidate C hsize c
  have hu : ∀q q' : Fin 3, (∃i, w q=p i) → (∃j, w q'=p j) → q=q' := by
    intro q q' hi hj
    obtain ⟨i,hi⟩ := hi
    obtain ⟨j,hj⟩ := hj
    exact arc_forbids_one hD hA C C hsize c (fun _ => rfl) p start hp q q' i j hi hj
  have hu' : ∀q q' : Fin 3, (∃i, w q=p' i) → (∃j, w q'=p' j) → q=q' := by
    intro q q' hi hj
    obtain ⟨i,hi⟩ := hi
    obtain ⟨j,hj⟩ := hj
    exact arc_forbids_one hD hA C C' hsize c hclock p' start' hp' q q' i j hi hj
  have hex : ∃q : Fin 3, (∀i, w q≠p i) ∧ (∀i, w q≠p' i) := by
    by_cases he : ∃q i, w q=p i
    · obtain ⟨q0,i0,hi0⟩ := he
      by_cases he' : ∃q i, w q=p' i
      · obtain ⟨q1,i1,hi1⟩ := he'
        obtain ⟨q,hq0,hq1⟩ := avoid_two q0 q1
        exact ⟨q,fun i hi => hq0 (hu q q0 ⟨i,hi⟩ ⟨i0,hi0⟩),
          fun i hi => hq1 (hu' q q1 ⟨i,hi⟩ ⟨i1,hi1⟩)⟩
      · obtain ⟨q,hq,_⟩ := avoid_two q0 q0
        exact ⟨q,fun i hi => hq (hu q q0 ⟨i,hi⟩ ⟨i0,hi0⟩),fun i hi => he' ⟨q,i,hi⟩⟩
    · by_cases he' : ∃q i, w q=p' i
      · obtain ⟨q1,i1,hi1⟩ := he'
        obtain ⟨q,hq,_⟩ := avoid_two q1 q1
        exact ⟨q,fun i hi => he ⟨q,i,hi⟩,fun i hi => hq (hu' q q1 ⟨i,hi⟩ ⟨i1,hi1⟩)⟩
      · exact ⟨0,fun i hi => he ⟨0,i,hi⟩,fun i hi => he' ⟨0,i,hi⟩⟩
  obtain ⟨q,hp0,hp1⟩ := hex
  have hc := candidate_phase C hsize c q
  exact ⟨w q,hc,(hclock _).symm.trans hc,hp0,hp1⟩

#print axioms prescribe_avoiding
end ErdePaths.PhaseArc
