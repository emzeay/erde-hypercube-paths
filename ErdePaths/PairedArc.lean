import ErdePaths.SquareArc
import ErdePaths.HamiltonData

namespace ErdePaths.PairedArc
open SourceClock SquareLift

/-- An actual directed segment of a literal cycle clock. Consecutive phases
are a consequence of step, not an assumed auxiliary coloring. -/
structure DirectedArc {V : Type} {N : Nat} (hN : 0<N) (C : ClockData V N) (A : Nat) where
  vertex : Fin (A+1)→V
  injective : Function.Injective vertex
  step : ∀i : Fin A, C.position (vertex i.succ)=successor hN (C.position (vertex i.castSucc))

theorem phase_consecutive {V N A D} (hN : 0<N) (C : ClockData V N)
    (p : DirectedArc hN C A) (hd : D∣N) (i : Fin (A+1)) :
    (C.position (p.vertex i)).val%D=((C.position (p.vertex ⟨0,by omega⟩)).val+i.val)%D := by
  have hh : ∀k (hk : k<A+1), (C.position (p.vertex ⟨k,hk⟩)).val%D=
      ((C.position (p.vertex ⟨0,by omega⟩)).val+k)%D := by
    intro k
    induction k with
    | zero => intro hk; simp only [Nat.add_zero]
    | succ k ih =>
      intro hk
      have hs := congrArg (fun t : Fin N => t.val%D) (p.step ⟨k,by omega⟩)
      change (C.position (p.vertex ⟨k+1,hk⟩)).val%D=
        (((C.position (p.vertex ⟨k,by omega⟩)).val+1)%N)%D at hs
      rw [Nat.mod_mod_of_dvd _ hd] at hs
      rw [Nat.add_mod,ih (by omega)] at hs
      simpa only [←Nat.add_mod,Nat.mod_mod,Nat.add_assoc] using hs
  exact hh i.val i.isLt

/-- Clock-step arcs in genuine cycle data use actual ambient graph edges. -/
theorem actual_adjacent {V : Type} {R : V→V→Prop} {N A : Nat} (hN : 0<N)
    (C : HamiltonData.CycleData V R N hN) (p : DirectedArc hN C.toClockData A) (i : Fin A) :
    R (p.vertex i.castSucc) (p.vertex i.succ) := by
  have ha := C.adjacent (C.position (p.vertex i.castSucc))
  rw [C.cycle_position] at ha
  have he : C.cycle (successor hN (C.position (p.vertex i.castSucc)))=p.vertex i.succ := by
    rw [←p.step,C.cycle_position]
  rw [he] at ha
  exact ha

def reverse {A : Nat} (i : Fin (A+1)) : Fin (A+1) := ⟨A-i.val,by have := i.isLt; omega⟩
theorem reverse_injective {A : Nat} : Function.Injective (@reverse A) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  change A-i.val=A-j.val at hh
  have := i.isLt
  have := j.isLt
  omega

/-- Literal same-coordinate lifted parent segment, with connectors avoided. -/
def lift {V N A} (hN : 0<N) (C : ClockData V N) (p : DirectedArc hN C A)
    (w : V) (avoid : ∀i, w≠p.vertex i) (b : Bool) :
    DirectedArc (Nat.mul_pos hN hN) (squareClock hN C b) A := by
  cases b
  · exact {
      vertex := fun i => (w,p.vertex (reverse i))
      injective := fun i j he => reverse_injective (p.injective (congrArg Prod.snd he))
      step := fun i => by
        let j : Fin A := ⟨A-(i.val+1),by have := i.isLt; omega⟩
        have hnext : j.castSucc=reverse i.succ := by apply Fin.ext; rfl
        have hprev : j.succ=reverse i.castSucc := by
          apply Fin.ext
          change A-(i.val+1)+1=A-i.val
          have := i.isLt
          omega
        have hs := p.step j
        rw [hnext,hprev] at hs
        exact SquareArc.plus_step hN C _ _ w hs (avoid _) }
  · exact {
      vertex := fun i => (p.vertex i,w)
      injective := fun i j he => p.injective (congrArg Prod.fst he)
      step := fun i => SquareArc.minus_step hN C _ _ w (p.step i) (avoid _) }


/-- Reduction of actual bounded DIFF positions, with subtraction performed
before reducing rather than silently truncating a reduced residue. -/
theorem difference_phase {N D i j : Nat} (hD : 0<D) (hd : D∣N) (hj : j<N) :
    (N-j+i)%D=(D-j%D+i%D)%D := by
  apply Int.natCast_inj.mp
  have hn : (N : Int)%(D : Int)=0 := by
    rw [←Int.natCast_emod,Nat.mod_eq_zero_of_dvd hd]; rfl
  have ht : ((N-j+i : Nat) : Int)=(N : Int)-(j : Int)+(i : Int) := by omega
  have hr : j%D<D := Nat.mod_lt _ hD
  have hu : ((D-j%D+i%D : Nat) : Int)=(D : Int)-(j%D : Int)+(i%D : Int) := by omega
  rw [Int.natCast_emod,Int.natCast_emod,ht,hu]
  have hjmod : (j%D : Int)%(D : Int)=(j : Int)%(D : Int) := by
    rw [Int.emod_emod]
  have himod : (i%D : Int)%(D : Int)=(i : Int)%(D : Int) := by
    rw [Int.emod_emod]
  conv => lhs; rw [Int.add_emod,Int.sub_emod,hn]
  conv => rhs; rw [Int.add_emod,Int.sub_emod,Int.emod_self,hjmod,himod]

private theorem backward_forward {D : Nat} (hD : 0<D) (i c : Fin D) :
    backward hD (forward hD i c) i=c :=
  forward_injective hD i (forward_inverse hD i (forward hD i c))

private theorem lift_start_phase {V N A D} (hN : 0<N) (hD : 0<D) (hd : D∣N)
    (C : ClockData V N) (p : DirectedArc hN C A) (w : V) (avoid : ∀i,w≠p.vertex i)
    (c : Fin D) (b : Bool)
    (hw : (C.position w).val%D=
      (if b then backward hD ⟨(C.position (p.vertex ⟨0,by omega⟩)).val%D,Nat.mod_lt _ hD⟩ c
        else forward hD ⟨(C.position (p.vertex ⟨A,by omega⟩)).val%D,Nat.mod_lt _ hD⟩ c).val) :
    ((squareClock hN C b).position ((lift hN C p w avoid b).vertex ⟨0,by omega⟩)).val%D=c.val := by
  rw [squareClock_mod hN hd]
  cases b
  · simp only [lift,reverse,Nat.sub_zero] at ⊢
    rw [difference_phase hD hd (C.position (p.vertex ⟨A,by omega⟩)).isLt]
    simp only [Bool.false_eq_true,ite_false] at hw
    rw [hw]
    exact congrArg Fin.val (backward_forward hD
      ⟨(C.position (p.vertex ⟨A,by omega⟩)).val%D,Nat.mod_lt _ hD⟩ c)
  · simp only [lift] at ⊢
    rw [difference_phase hD hd (C.position w).isLt]
    simp only [ite_true] at hw
    rw [hw]
    exact congrArg Fin.val (backward_inverse hD
      ⟨(C.position (p.vertex ⟨0,by omega⟩)).val%D,Nat.mod_lt _ hD⟩ c)

/-- One actual common-phase vertex avoids both whole parent arcs and gives
both lifted arcs arbitrary prescribed new start phase and common endpoints. -/
theorem paired_lift {V N A D} (hN : 0<N) (hD : 0<D) (hd : D∣N)
    (hA : A<D) (hsize : 3*D≤N) (C C' : ClockData V N)
    (hc : ∀v, (C.position v).val%D=(C'.position v).val%D)
    (p : DirectedArc hN C A) (p' : DirectedArc hN C' A)
    (hstart : p.vertex ⟨0,by omega⟩=p'.vertex ⟨0,by omega⟩)
    (hend : p.vertex ⟨A,by omega⟩=p'.vertex ⟨A,by omega⟩)
    (c : Fin D) (b : Bool) :
    ∃w, ∃avoid : ∀i,w≠p.vertex i, ∃avoid' : ∀i,w≠p'.vertex i,
      (lift hN C p w avoid b).vertex ⟨0,by omega⟩=
        (lift hN C' p' w avoid' b).vertex ⟨0,by omega⟩ ∧
      (lift hN C p w avoid b).vertex ⟨A,by omega⟩=
        (lift hN C' p' w avoid' b).vertex ⟨A,by omega⟩ ∧
      ((squareClock hN C b).position ((lift hN C p w avoid b).vertex ⟨0,by omega⟩)).val%D=c.val ∧
      ((squareClock hN C' b).position ((lift hN C' p' w avoid' b).vertex ⟨0,by omega⟩)).val%D=c.val := by
  let start := (C.position (p.vertex ⟨0,by omega⟩)).val
  let finish := (C.position (p.vertex ⟨A,by omega⟩)).val
  let target : Fin D := if b then backward hD ⟨start%D,Nat.mod_lt _ hD⟩ c
    else forward hD ⟨finish%D,Nat.mod_lt _ hD⟩ c
  obtain ⟨w,hw,hw',avoid,avoid'⟩ := PhaseArc.prescribe_avoiding hD hA C C' hsize target hc
    p.vertex p'.vertex start (C'.position (p'.vertex ⟨0,by omega⟩)).val
    (phase_consecutive hN C p hd) (phase_consecutive hN C' p' hd)
  refine ⟨w,avoid,avoid',?_,?_,?_,?_⟩
  · cases b
    · change (w,p.vertex ⟨A,by omega⟩)=(w,p'.vertex ⟨A,by omega⟩)
      rw [hend]
    · change (p.vertex ⟨0,by omega⟩,w)=(p'.vertex ⟨0,by omega⟩,w)
      rw [hstart]
  · cases b
    · simp only [lift,reverse,Nat.sub_self]
      rw [hstart]
    · change (p.vertex ⟨A,by omega⟩,w)=(p'.vertex ⟨A,by omega⟩,w)
      rw [hend]
  · exact lift_start_phase hN hD hd C p w avoid c b hw
  · apply lift_start_phase hN hD hd C' p' w avoid' c b
    have hs : (C.position (p.vertex ⟨0,by omega⟩)).val%D=(C'.position (p'.vertex ⟨0,by omega⟩)).val%D :=
      (hc _).trans (congrArg (fun v => (C'.position v).val%D) hstart)
    have he : (C.position (p.vertex ⟨A,by omega⟩)).val%D=(C'.position (p'.vertex ⟨A,by omega⟩)).val%D :=
      (hc _).trans (congrArg (fun v => (C'.position v).val%D) hend)
    simpa only [target,start,finish,hs,he] using hw'

/-- The whole prescribed phase progression follows from genuine lifted steps,
including cyclic seams; it is never an independent arc field. -/
theorem paired_lift_phases {V N A D} (hN : 0<N) (hD : 0<D) (hd : D∣N)
    (hA : A<D) (hsize : 3*D≤N) (C C' : ClockData V N)
    (hc : ∀v, (C.position v).val%D=(C'.position v).val%D)
    (p : DirectedArc hN C A) (p' : DirectedArc hN C' A)
    (hstart : p.vertex ⟨0,by omega⟩=p'.vertex ⟨0,by omega⟩)
    (hend : p.vertex ⟨A,by omega⟩=p'.vertex ⟨A,by omega⟩)
    (c : Fin D) (b : Bool) :
    ∃w, ∃avoid : ∀i,w≠p.vertex i, ∃avoid' : ∀i,w≠p'.vertex i,
      (lift hN C p w avoid b).vertex ⟨0,by omega⟩=
        (lift hN C' p' w avoid' b).vertex ⟨0,by omega⟩ ∧
      (lift hN C p w avoid b).vertex ⟨A,by omega⟩=
        (lift hN C' p' w avoid' b).vertex ⟨A,by omega⟩ ∧
      ∀i, ((squareClock hN C b).position ((lift hN C p w avoid b).vertex i)).val%D=(c.val+i.val)%D ∧
        ((squareClock hN C' b).position ((lift hN C' p' w avoid' b).vertex i)).val%D=(c.val+i.val)%D := by
  obtain ⟨w,av,av',hs,he,hp,hp'⟩ := paired_lift hN hD hd hA hsize C C' hc p p' hstart hend c b
  refine ⟨w,av,av',hs,he,?_⟩
  intro i
  have hdnew : D∣N*N := Nat.dvd_trans hd (Nat.dvd_mul_right N N)
  constructor
  · have hh := phase_consecutive (Nat.mul_pos hN hN) (squareClock hN C b) (lift hN C p w av b) hdnew i
    rw [Nat.add_mod,hp] at hh
    simpa only [Nat.add_mod_mod] using hh
  · have hh := phase_consecutive (Nat.mul_pos hN hN) (squareClock hN C' b) (lift hN C' p' w av' b) hdnew i
    rw [Nat.add_mod,hp'] at hh
    simpa only [Nat.add_mod_mod] using hh

#print axioms paired_lift_phases
#print axioms paired_lift
#print axioms phase_consecutive
#print axioms lift
end ErdePaths.PairedArc
