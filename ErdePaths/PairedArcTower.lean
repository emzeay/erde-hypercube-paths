import ErdePaths.PairedArc
import ErdePaths.ProfileLift

namespace ErdePaths.PairedArcTower
open SourceClock SquareLift PairedArc

/-- Repeated genuine squares never shorten a positive parent clock. -/
theorem lengthPower_ge {N : Nat} (hN : 0<N) (k : Nat) : N≤lengthPower N k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have hpos := lengthPower_positive hN k
    have hm := Nat.mul_le_mul_left (lengthPower N k) (show 1≤lengthPower N k by omega)
    simp only [Nat.mul_one] at hm
    change N≤lengthPower N k*lengthPower N k
    omega

/-- Arbitrary-depth paired upper lift. Both twins follow the SAME upper
branch address; the fixed-coordinate choices are constructed at every stage.
At least one lift is needed to prescribe an arbitrary new start phase. -/
theorem paired_tower {V : Type} {N A D : Nat} (hN : 0<N) (hD : 0<D) (hd : D∣N)
    (hA : A<D) (hsize : 3*D≤N) (C C' : ClockData V N)
    (hc : ∀v, (C.position v).val%D=(C'.position v).val%D)
    (p : DirectedArc hN C A) (p' : DirectedArc hN C' A)
    (hstart : p.vertex ⟨0,by omega⟩=p'.vertex ⟨0,by omega⟩)
    (hend : p.vertex ⟨A,by omega⟩=p'.vertex ⟨A,by omega⟩)
    (k : Nat) (address : Fin (k+1)→Bool) (c : Fin D) :
    ∃q : DirectedArc (lengthPower_positive hN (k+1)) (iteratedClock hN C (k+1) address) A,
    ∃q' : DirectedArc (lengthPower_positive hN (k+1)) (iteratedClock hN C' (k+1) address) A,
      q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
      q.vertex ⟨A,by omega⟩=q'.vertex ⟨A,by omega⟩ ∧
      ∀i, ((iteratedClock hN C (k+1) address).position (q.vertex i)).val%D=(c.val+i.val)%D ∧
        ((iteratedClock hN C' (k+1) address).position (q'.vertex i)).val%D=(c.val+i.val)%D := by
  induction k generalizing c with
  | zero =>
    obtain ⟨w,av,av',hs,he,hp⟩ := paired_lift_phases hN hD hd hA hsize C C' hc p p' hstart hend c (address 0)
    exact ⟨lift hN C p w av (address 0),lift hN C' p' w av' (address 0),hs,he,hp⟩
  | succ k ih =>
    let lower : Fin (k+1)→Bool := fun i => address i.castSucc
    obtain ⟨q,q',hs,he,hp⟩ := ih lower ⟨0,hD⟩
    have hdk := lengthPower_divisible hd (k+1)
    have hsz : 3*D≤lengthPower N (k+1) := Nat.le_trans hsize (lengthPower_ge hN (k+1))
    have hck : ∀v, ((iteratedClock hN C (k+1) lower).position v).val%D=
        ((iteratedClock hN C' (k+1) lower).position v).val%D :=
      descendants_common_clock hN hd C C' hc (k+1) lower lower
    obtain ⟨w,av,av',hs',he',hp'⟩ := paired_lift_phases (lengthPower_positive hN (k+1)) hD hdk hA hsz
      (iteratedClock hN C (k+1) lower) (iteratedClock hN C' (k+1) lower) hck q q' hs he c (address (Fin.last (k+1)))
    exact ⟨lift _ _ q w av (address (Fin.last (k+1))),lift _ _ q' w av' (address (Fin.last (k+1))),hs',he',hp'⟩

/-- Actual base-profile arcs are constructed from the literal first-round
profile tour and its checked inverse clock, never supplied as existence data. -/
noncomputable def profileArc {V : Type} {e A : Nat} (he : 1≤e)
    (C : ClockData V (2^e)) (hA : A<2^e) (S : Fin (2^e)→Bool)
    (ho : Profile.cardinality S%2=1) (color : Bool) :
    DirectedArc (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
      (ProfileLift.clock he C S ho color) A where
  vertex := ProfileLift.liftedArc C hA S color
  injective := ProfileLift.liftedArc_simple he C hA S ho color
  step i := by
    rw [ProfileLift.liftedArc_clock,ProfileLift.liftedArc_clock]
    apply Fin.ext
    change i.val+1=(i.val+1)%((2^e)*(2^e))
    have hh := (ProfileArcs.arcIndex (Nat.two_pow_pos e) hA i.succ).isLt
    exact (Nat.mod_eq_of_lt hh).symm

/-- The two genuine complementary profile arcs have the same physical start. -/
theorem profileArc_start {V : Type} {e A : Nat} (he : 1≤e)
    (C : ClockData V (2^e)) (hA : A<2^e) (S : Fin (2^e)→Bool)
    (ho : Profile.cardinality S%2=1) (color : Bool) :
    (profileArc he C hA S ho color).vertex ⟨0,by omega⟩=
      (C.cycle ⟨0,Nat.two_pow_pos e⟩,C.cycle ⟨0,Nat.two_pow_pos e⟩) := by
  change ProfileLift.map C (ProfileArcs.arc _ hA S color ⟨0,by omega⟩)=_
  rw [ProfileArcs.arc_start]
  rfl

/-- Uniform concrete profile-to-upper-tower geometry. Only numeric selector
conditions are supplied; the common directed base arcs are constructed here. -/
theorem profile_paired_tower {V : Type} {e u D : Nat} (he : 1≤e) (hD : 0<D) (hd : D∣2^e)
    (hu : 2*u<2^e) (hshort : 2*u<D) (hsize : 3*D≤(2^e)*(2^e))
    (C : ClockData V (2^e)) (S : Fin (2^e)→Bool) (ho : Profile.cardinality S%2=1)
    (hbalance : Profile.prefixCount S (2*u)=u) (k : Nat) (address : Fin (k+1)→Bool) (c : Fin D) :
    ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1))
        (iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
          (ProfileLift.clock he C S ho false) (k+1) address) (2*u),
    ∃q' : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1))
        (iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
          (ProfileLift.clock he C S ho true) (k+1) address) (2*u),
      q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
      q.vertex ⟨2*u,by omega⟩=q'.vertex ⟨2*u,by omega⟩ ∧
      ∀i, ((iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
          (ProfileLift.clock he C S ho false) (k+1) address).position (q.vertex i)).val%D=(c.val+i.val)%D ∧
        ((iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
          (ProfileLift.clock he C S ho true) (k+1) address).position (q'.vertex i)).val%D=(c.val+i.val)%D := by
  let p := profileArc he C hu S ho false
  let p' := profileArc he C hu S ho true
  have hs : p.vertex ⟨0,by omega⟩=p'.vertex ⟨0,by omega⟩ := by
    rw [profileArc_start,profileArc_start]
  have hend (color : Bool) : (profileArc he C hu S ho color).vertex ⟨2*u,by omega⟩=
      (C.cycle ⟨u,by omega⟩,C.cycle ⟨u,by omega⟩) := by
    exact ProfileLift.liftedArc_balanced_end C hu S hbalance color
  have he' : p.vertex ⟨2*u,by omega⟩=p'.vertex ⟨2*u,by omega⟩ := (hend false).trans (hend true).symm
  exact paired_tower (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) hD
    (Nat.dvd_trans hd (Nat.dvd_mul_right (2^e) (2^e))) hshort hsize
    (ProfileLift.clock he C S ho false) (ProfileLift.clock he C S ho true)
    (ProfileLift.common_clock he hd C C (fun _ => rfl) S S ho ho false true)
    p p' hs he' k address c

/-- Zero upper depth retains the literal base start phase 0. Arbitrary phase
prescription at this boundary is deliberately not asserted. -/
theorem profile_zero_phases {V : Type} {e A D : Nat} (he : 1≤e)
    (C : ClockData V (2^e)) (hA : A<2^e) (S : Fin (2^e)→Bool)
    (ho : Profile.cardinality S%2=1) (color : Bool) (i : Fin (A+1)) :
    ((ProfileLift.clock he C S ho color).position ((profileArc he C hA S ho color).vertex i)).val%D=i.val%D := by
  change ((ProfileLift.clock he C S ho color).position (ProfileLift.liftedArc C hA S color i)).val%D=_
  rw [ProfileLift.liftedArc_clock]
  rfl

theorem profile_room {e D : Nat} (he : 2≤e) (hd : D∣2^e) : 3*D≤(2^e)*(2^e) := by
  have h4 : 4≤2^e := by
    have hh := Nat.pow_le_pow_right (show 1≤2 by decide) he
    omega
  have hdn : D≤2^e := Nat.le_of_dvd (Nat.two_pow_pos e) hd
  calc
    3*D≤3*(2^e) := Nat.mul_le_mul_left 3 hdn
    _=(2^e)*3 := Nat.mul_comm _ _
    _≤(2^e)*(2^e) := Nat.mul_le_mul_left (2^e) (by omega)

/-- Concrete uniform interval-selector specialization: its odd cardinality
and balanced prefix are proved, not assumed auxiliary arc existence. -/
theorem interval_profile_tower {V : Type} {e u D : Nat} (he : 2≤e) (hD : 0<D) (hd : D∣2^e)
    (hu : 2*u<2^e) (hshort : 2*u<D) (huEven : u%2=0)
    (C : ClockData V (2^e)) (k : Nat) (address : Fin (k+1)→Bool) (c : Fin D) :
    let S := Profile.intervalWithEndpoint (N:=2^e) u
    let ho := Profile.intervalWithEndpoint_odd hu huEven
    let F := fun color => iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
      (ProfileLift.clock (show 1≤e by omega) C S ho color) (k+1) address
    ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1)) (F false) (2*u),
    ∃q' : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1)) (F true) (2*u),
      q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
      q.vertex ⟨2*u,by omega⟩=q'.vertex ⟨2*u,by omega⟩ ∧
      ∀i, ((F false).position (q.vertex i)).val%D=(c.val+i.val)%D ∧
        ((F true).position (q'.vertex i)).val%D=(c.val+i.val)%D := by
  intro S ho F
  exact profile_paired_tower (by omega) hD hd hu hshort (profile_room he hd) C S ho
    (Profile.intervalWithEndpoint_balanced_prefix hu) k address c

/-- A=2 uses the actual singleton selector, avoiding the false assertion that
an odd-half interval selector has odd cardinality. -/
theorem singleton_profile_tower {V : Type} {e D : Nat} (he : 2≤e) (hD : 0<D) (hd : D∣2^e)
    (hshort : 2<D) (C : ClockData V (2^e)) (k : Nat) (address : Fin (k+1)→Bool) (c : Fin D) :
    let S := Profile.intervalWithEndpoint (N:=2^e) 0
    let ho : Profile.cardinality S%2=1 := Profile.intervalWithEndpoint_odd (by have := Nat.two_pow_pos e; omega) rfl
    let F := fun color => iteratedClock (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e))
      (ProfileLift.clock (show 1≤e by omega) C S ho color) (k+1) address
    ∃q : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1)) (F false) 2,
    ∃q' : DirectedArc (lengthPower_positive (Nat.mul_pos (Nat.two_pow_pos e) (Nat.two_pow_pos e)) (k+1)) (F true) 2,
      q.vertex ⟨0,by omega⟩=q'.vertex ⟨0,by omega⟩ ∧
      q.vertex ⟨2,by omega⟩=q'.vertex ⟨2,by omega⟩ ∧
      ∀i, ((F false).position (q.vertex i)).val%D=(c.val+i.val)%D ∧
        ((F true).position (q'.vertex i)).val%D=(c.val+i.val)%D := by
  intro S ho F
  have h2 : 2<2^e := by
    have hh := Nat.pow_le_pow_right (show 1≤2 by decide) he
    omega
  have hp : Profile.prefixCount S (2*1)=1 := by
    change Profile.prefixCount (Profile.intervalWithEndpoint (N:=2^e) 0) 2=1
    rw [Profile.intervalWithEndpoint_prefix 0 2 (by omega)]
    rfl
  exact profile_paired_tower (u := 1) (by omega) hD hd h2 hshort (profile_room he hd) C S ho hp k address c

#print axioms interval_profile_tower
#print axioms singleton_profile_tower
#print axioms profileArc
#print axioms profile_paired_tower
#print axioms paired_tower
end ErdePaths.PairedArcTower
