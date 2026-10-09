import ErdePaths.Profile

namespace ErdePaths.ProfileArcs
open SquareLift SourceClock Profile

/-- Actual first-round clock positions, retaining both endpoints. -/
def arcIndex {N A : Nat} (hN : 0<N) (hA : A<N) (i : Fin (A+1)) : Fin (N*N) :=
  ⟨i.val,by
    have hi : i.val<N := by have := i.isLt; omega
    have hm : N≤N*N := by
      have hh := Nat.mul_le_mul_left N (show 1≤N by omega)
      simpa only [Nat.mul_one] using hh
    omega⟩

theorem arcIndex_injective {N A : Nat} (hN : 0<N) (hA : A<N) :
    Function.Injective (arcIndex hN hA) := by
  intro i j h
  have hv := congrArg (fun z : Fin (N*N) => z.val) h
  exact Fin.ext hv

/-- A path restriction of the actual numeric profile cycle, not a new
path-existence assumption. -/
def arc {N A : Nat} (hN : 0<N) (hA : A<N) (S : Fin N → Bool) (color : Bool) :
    Fin (A+1) → Profile.Vertex N := fun i => profileCycles hN S color (arcIndex hN hA i)

theorem arc_first_round {N A : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) (i : Fin (A+1)) :
    arc hN hA S color i = profileVertex hN (colorSet S color)
      (⟨0,hN⟩,⟨i.val,by have := i.isLt; omega⟩) := by
  unfold arc profileCycles profileTour
  congr 1
  apply Prod.ext <;> apply Fin.ext
  · exact Nat.div_eq_of_lt (show i.val<N from by have := i.isLt; omega)
  · exact Nat.mod_eq_of_lt (show i.val<N from by have := i.isLt; omega)

theorem arc_directed {N A : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) (i : Fin A) :
    arc hN hA S color i.succ = step hN S color (arc hN hA S color i.castSucc) := by
  have hn : arcIndex hN hA i.succ = successor (Nat.mul_pos hN hN) (arcIndex hN hA i.castSucc) := by
    apply Fin.ext
    have hlt := (arcIndex hN hA i.succ).isLt
    change i.val+1 = (i.val+1)%(N*N)
    exact (Nat.mod_eq_of_lt hlt).symm
  unfold arc
  rw [hn,profileCycles_next]

theorem arc_adjacent {N A : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) (i : Fin A) :
    TorusAdjacent hN (arc hN hA S color i.castSucc) (arc hN hA S color i.succ) := by
  rw [arc_directed]
  refine ⟨stepLabel hN S color (arc hN hA S color i.castSucc),?_⟩
  rw [step_decodes]
  exact Or.inl rfl

theorem arc_simple {e A : Nat} (he : 1≤e) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (hodd : cardinality S%2=1) (color : Bool) :
    Function.Injective (arc (Nat.two_pow_pos e) hA S color) := by
  intro i j hij
  exact arcIndex_injective _ _ (profileCycles_injective he S hodd color hij)

/-- Actual inverse clock coordinates of every arc vertex are its index. -/
theorem arc_clock {e A : Nat} (he : 1≤e) (hA : A<2^e)
    (S : Fin (2^e) → Bool) (hodd : cardinality S%2=1) (color : Bool) (i : Fin (A+1)) :
    (profileClockData he S hodd color).position (arc (Nat.two_pow_pos e) hA S color i)
      = arcIndex (Nat.two_pow_pos e) hA i := by
  exact (profileClockData he S hodd color).position_cycle _

theorem arc_start {N A : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) :
    arc hN hA S color ⟨0,by omega⟩=(⟨0,hN⟩,⟨0,hN⟩) := by
  rw [arc_first_round]
  apply Prod.ext <;> apply Fin.ext <;>
    simp [profileVertex,prefixCount,backward]

theorem arc_balanced_end {N u : Nat} (hN : 0<N) (hu : 2*u<N)
    (S : Fin N → Bool) (hp : prefixCount S (2*u)=u) (color : Bool) :
    arc hN hu S color (Fin.last (2*u))=(⟨u,by omega⟩,⟨u,by omega⟩) := by
  rw [arc_first_round]
  exact balanced_prefix_endpoint hN hu S hp color


/-- Natural (nonwrapping) coordinates of a first-round arc vertex. -/
theorem arc_coordinates {N A p : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) (i : Fin (A+1))
    (hp : prefixCount (colorSet S color) i.val=p) (hpi : p≤i.val) :
    arc hN hA S color i =
      (⟨p,by have := i.isLt; omega⟩,⟨i.val-p,by have := i.isLt; omega⟩) := by
  have hi : i.val<N := by have := i.isLt; omega
  have hpn : p<N := by omega
  rw [arc_first_round]
  apply Prod.ext <;> apply Fin.ext
  · simp only [profileVertex,hp,Nat.zero_mul,Nat.zero_add,Nat.mod_eq_of_lt hpn]
  · simp only [profileVertex,hp,Nat.zero_mul,Nat.zero_add,Nat.mod_eq_of_lt hpn,backward]
    have he : N-p+i.val=N+(i.val-p) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (show i.val-p<N by omega)]

/-- The interval profile's first arc is literally x^u y^u; the other
profile's arc is y^u x^u. This formula retains every intermediate vertex. -/
theorem interval_arc_coordinates {N u : Nat} (hN : 0<N) (hu : 2*u<N)
    (color : Bool) (i : Fin (2*u+1)) :
    arc hN hu (intervalWithEndpoint u) color i =
      if color then
        (⟨i.val-Nat.min i.val u,by have := i.isLt; omega⟩,
         ⟨Nat.min i.val u,by exact Nat.lt_of_le_of_lt (Nat.min_le_right i.val u) (by omega)⟩)
      else
        (⟨Nat.min i.val u,by exact Nat.lt_of_le_of_lt (Nat.min_le_right i.val u) (by omega)⟩,
         ⟨i.val-Nat.min i.val u,by have := i.isLt; omega⟩) := by
  have hi : i.val≤2*u := by have := i.isLt; omega
  have hp : prefixCount (intervalWithEndpoint (N:=N) u) i.val=Nat.min i.val u := by
    rw [intervalWithEndpoint_prefix u i.val (by omega)]
    rw [ite_eq_right (show ¬2*u<i.val by omega),Nat.add_zero]
  cases color
  · have hs : colorSet (intervalWithEndpoint (N:=N) u) false=intervalWithEndpoint u := by
      funext h; exact Bool.xor_false _
    have hp' : prefixCount (colorSet (intervalWithEndpoint (N:=N) u) false) i.val=Nat.min i.val u := by
      rw [hs]; exact hp
    exact arc_coordinates hN hu _ false i hp' (Nat.min_le_left _ _)
  · have hc := prefixCount_complement (intervalWithEndpoint (N:=N) u) i.val (by omega)
    have hp' : prefixCount (colorSet (intervalWithEndpoint (N:=N) u) true) i.val=i.val-Nat.min i.val u := by
      rw [hp] at hc
      have := Nat.min_le_left i.val u
      omega
    have h := arc_coordinates hN hu _ true i hp' (by omega)
    have he : i.val-(i.val-Nat.min i.val u)=Nat.min i.val u := by
      have := Nat.min_le_left i.val u
      omega
    simpa only [he,↓reduceIte] using h

/-- Complete uniform simple common directed arc in an odd interval profile.
The hypotheses state exactly when this profile is Hamilton: even u and 2u<N. -/
theorem interval_common_arc {e u : Nat} (he : 2≤e) (hu : 2*u<2^e) (huEven : u%2=0) :
    let S := intervalWithEndpoint (N:=2^e) u
    let hodd := intervalWithEndpoint_odd hu huEven
    ∀ color : Bool,
      Function.Injective (arc (Nat.two_pow_pos e) hu S color) ∧
      (∀ i : Fin (2*u), arc (Nat.two_pow_pos e) hu S color i.succ =
        step (Nat.two_pow_pos e) S color (arc (Nat.two_pow_pos e) hu S color i.castSucc)) ∧
      arc (Nat.two_pow_pos e) hu S color ⟨0,by omega⟩=(⟨0,Nat.two_pow_pos e⟩,⟨0,Nat.two_pow_pos e⟩) ∧
      arc (Nat.two_pow_pos e) hu S color (Fin.last (2*u))=(⟨u,by omega⟩,⟨u,by omega⟩) ∧
      (∀ i, (profileClockData (show 1≤e by omega) S hodd color).position
        (arc (Nat.two_pow_pos e) hu S color i)=arcIndex (Nat.two_pow_pos e) hu i) := by
  intro S hodd color
  exact ⟨arc_simple (by omega) hu S hodd color,
    arc_directed _ hu S color,arc_start _ hu S color,
    arc_balanced_end _ hu S (intervalWithEndpoint_balanced_prefix hu) color,
    arc_clock (by omega) hu S hodd color⟩


theorem arc_height {N A : Nat} (hN : 0<N) (hA : A<N)
    (S : Fin N → Bool) (color : Bool) (i : Fin (A+1)) :
    (height hN (arc hN hA S color i)).val=i.val := by
  rw [arc_first_round,profileVertex_height]

/-- The two literal interval arcs have no common interior vertex. -/
theorem interval_arc_cross_eq {N u : Nat} (hN : 0<N) (hu : 2*u<N)
    (i j : Fin (2*u+1))
    (h : arc hN hu (intervalWithEndpoint u) false i =
      arc hN hu (intervalWithEndpoint u) true j) :
    i=j ∧ (i.val=0 ∨ i.val=2*u) := by
  have hh := congrArg (fun v : Profile.Vertex N => (height hN v).val) h
  rw [arc_height,arc_height] at hh
  have hij : i=j := Fin.ext hh
  subst j
  rw [interval_arc_coordinates,interval_arc_coordinates] at h
  simp only [Bool.false_eq_true,↓reduceIte] at h
  have hx := congrArg (fun v : Profile.Vertex N => v.1.val) h
  change Nat.min i.val u=i.val-Nat.min i.val u at hx
  simp only [Nat.min,Nat.min_def] at hx
  split at hx <;> omega

/-- A=2 uses the singleton profile, rather than the even-cardinality u=1
interval profile. Its two first steps have the same literal endpoint. -/
theorem singleton_common_two_arc {e : Nat} (he : 2≤e) :
    let hA : 2<2^e := by
      have hh := Nat.pow_le_pow_right (show 1≤2 by decide) he
      omega
    let S := intervalWithEndpoint (N:=2^e) 0
    let hodd : cardinality S%2=1 := intervalWithEndpoint_odd (by omega) rfl
    ∀ color : Bool,
      Function.Injective (arc (Nat.two_pow_pos e) hA S color) ∧
      (∀ i : Fin 2, arc (Nat.two_pow_pos e) hA S color i.succ =
        step (Nat.two_pow_pos e) S color (arc (Nat.two_pow_pos e) hA S color i.castSucc)) ∧
      arc (Nat.two_pow_pos e) hA S color ⟨0,by omega⟩=(⟨0,Nat.two_pow_pos e⟩,⟨0,Nat.two_pow_pos e⟩) ∧
      arc (Nat.two_pow_pos e) hA S color (Fin.last 2)=(⟨1,by omega⟩,⟨1,by omega⟩) ∧
      (∀ i, (profileClockData (show 1≤e by omega) S hodd color).position
        (arc (Nat.two_pow_pos e) hA S color i)=arcIndex (Nat.two_pow_pos e) hA i) := by
  intro hA S hodd color
  have hp : prefixCount S (2*1)=1 := by
    change prefixCount (intervalWithEndpoint (N:=2^e) 0) 2=1
    rw [intervalWithEndpoint_prefix 0 2 (by omega)]
    rfl
  exact ⟨arc_simple (by omega) hA S hodd color,
    arc_directed _ hA S color,arc_start _ hA S color,
    arc_balanced_end _ hA S hp color,arc_clock (by omega) hA S hodd color⟩

#print axioms interval_common_arc
#print axioms interval_arc_coordinates
#print axioms singleton_common_two_arc

end ErdePaths.ProfileArcs
