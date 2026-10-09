import ErdePaths.QuarterProfileOrigins
import ErdePaths.BaselinePhysical
import ErdePaths.SourceLengths
import ErdePaths.SourceAnchorCoordinates
import ErdePaths.QuarterPatternGeometry

namespace ErdePaths.QuarterPhysicalIncidence
open SourceClock SourceProfile HierarchicalDecode SquareLift QuarterProfileOrigins
open AACResidueBridge OrientedClock
attribute [local instance] Classical.propDecidable

abbrev K (e : Nat) := 2^(e*2^2-1)

section Actual
variable {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))

include he in
theorem length_eq : (2^(e*2^1))*(2^(e*2^1))=K e*2 := by
  simpa only [lengthPower,Nat.pow_zero,Nat.pow_one] using SourceLengths.fine_length he 1 0 1 (by decide)

noncomputable def raw (epsilon : Bool) (a : Address 1) :
    ClockData (VertexPower V 1×VertexPower V 1) (K e*2) :=
  castClock (length_eq he) (QuarterProfileOrigins.clock he C epsilon a)

noncomputable def endpoint (epsilon : Bool) (a : Address 1) : Fin (K e*2) :=
  Fin.cast (length_eq he) (origin he C epsilon a)

/-- Reoriented at the actual paired endpoint, with positive threshold one. -/
noncomputable def oriented (epsilon : Bool) (a : Address 1) :
    ClockData (VertexPower V 1×VertexPower V 1) (K e*2) :=
  OrientedClock.clock (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (raw he C epsilon a)
    (OrientedClock.index (Nat.mul_pos (Nat.two_pow_pos _) (by decide)) (endpoint he C epsilon a)
      (!epsilon) (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2))) epsilon

include he in
theorem period : 4∣K e := by
  exact Nat.pow_dvd_pow 2 (show 2≤e*2^2-1 by have := Nat.mul_le_mul_right 4 he; omega)

theorem raw_position (epsilon : Bool) (a : Address 1) (v : VertexPower V 1×VertexPower V 1) :
    ((raw he C epsilon a).position v).val=((QuarterProfileOrigins.clock he C epsilon a).position v).val :=
  SourceProfile.castClock_position (length_eq he) (QuarterProfileOrigins.clock he C epsilon a) v

/-- Actual baseline quarter marks are exactly the genuine physical quarter
owner class of the paired endpoint. No membership/ownership hypothesis. -/
theorem baseline_iff {B : Nat} (epsilon : Bool) (a : Address 1)
    (v : VertexPower V 1×VertexPower V 1) (j : Fin B) :
    AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w=>QuarterPatternGeometry.quarter w.1)
      (⟨1,by decide⟩ : Fin 2) ((oriented he C epsilon a).position v,j) ↔
      ((QuarterProfileOrigins.clock he C epsilon a).position v).val%4=code epsilon a := by
  have hc : (endpoint he C epsilon a).val%(2*2)=(⟨code epsilon a,code_lt epsilon a⟩ : Fin 4).val :=
    origin_code he C epsilon a
  have hh := BaselinePhysical.anti_physical_classes (Nat.two_pow_pos _) (by decide : 0<2)
    (by decide : 0<2) (period he) (by decide : 1<2) (by decide : 2%2=0) (by decide : 1%2=1)
    (raw he C epsilon a) (endpoint he C epsilon a) (⟨code epsilon a,code_lt epsilon a⟩ : Fin 4)
    hc (⟨1,by decide⟩ : Fin 2) epsilon v j
  change _ ↔ ∃u : Fin 1, shiftedResidue 4 (SourceStability.signedOffset 4 2 u.val (!epsilon))
    ((raw he C epsilon a).position v).val=code epsilon a at hh
  refine hh.trans ?_
  constructor
  · rintro ⟨u,hu⟩
    have hz : u.val=0 := by have := u.isLt; omega
    rw [raw_position] at hu
    simpa [hz,SourceStability.signedOffset,shiftedResidue] using hu
  · intro hv
    refine ⟨⟨0,by decide⟩,?_⟩
    rw [raw_position]
    simpa [SourceStability.signedOffset,shiftedResidue] using hv

/-- Exact old spacing-two anchor class of the same literal reoriented clock. -/
theorem anchor_iff (epsilon : Bool) (a : Address 1) (v : VertexPower V 1×VertexPower V 1) :
    ((oriented he C epsilon a).position v).val%2=0 ↔
      (((QuarterProfileOrigins.clock he C epsilon a).position v).val+1)%2=(code epsilon a)%2 := by
  have hh := SourceAnchorCoordinates.grid_residue_iff
    (Nat.mul_pos (Nat.two_pow_pos _) (by decide : 0<2)) (by decide : 0<2)
    (Nat.dvd_mul_left 2 (K e)) (raw he C epsilon a) (endpoint he C epsilon a)
    (BaselinePhysical.threshold (Nat.two_pow_pos _) (⟨1,by decide⟩ : Fin 2)) epsilon v
  have hc : (endpoint he C epsilon a).val%2=code epsilon a%2 := by
    have hc := origin_code he C epsilon a
    have hz := congrArg (fun n=>n%2) hc
    simpa only [Nat.mod_mod_of_dvd _ (by decide : 2∣4),endpoint,Fin.val_cast] using hz
  rw [hc] at hh
  change _ ↔ shiftedResidue 2 (SourceStability.signedOffset 2 1 1 epsilon)
    ((raw he C epsilon a).position v).val=code epsilon a%2 at hh
  refine hh.trans ?_
  rw [raw_position]
  cases epsilon <;> simp [SourceStability.signedOffset,shiftedResidue]

/-- Exactly one of the four ACTUAL baseline marked source clocks owns
each physical first-axis vertex in every row. -/
theorem unique_baseline_owner {B : Nat} (v : VertexPower V 1×VertexPower V 1) (j : Fin B) :
    ∃epsilon a,
      AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w=>QuarterPatternGeometry.quarter w.1)
        (⟨1,by decide⟩ : Fin 2) ((oriented he C epsilon a).position v,j) ∧
      ∀epsilon' a', AACMarkIntervals.IsMark (Nat.two_pow_pos _) (fun w=>QuarterPatternGeometry.quarter w.1)
        (⟨1,by decide⟩ : Fin 2) ((oriented he C epsilon' a').position v,j)→
        epsilon'=epsilon ∧ a'=a := by
  obtain ⟨eps,a,ha,hu⟩ := unique_quarter_owner he C v
  exact ⟨eps,a,(baseline_iff he C eps a v j).mpr ha,
    fun eps' a' hh=>hu eps' a' ((baseline_iff he C eps' a' v j).mp hh)⟩

/-- In EACH old orientation group, exactly one of its two actual source
factors has the vertex on its spacing-two grid. -/
theorem unique_anchor_owner (epsilon : Bool) (v : VertexPower V 1×VertexPower V 1) :
    ∃a : Address 1, ((oriented he C epsilon a).position v).val%2=0 ∧
      ∀a', ((oriented he C epsilon a').position v).val%2=0→a'=a := by
  let n := ((QuarterProfileOrigins.clock he C false (address false)).position v).val
  have hc (a : Address 1) : ((QuarterProfileOrigins.clock he C epsilon a).position v).val%2=n%2 := by
    have hh := common_mod_four he C epsilon false a (address false) v
    have hh' := congrArg (fun k=>k%2) hh
    simpa only [Nat.mod_mod_of_dvd _ (by decide : 2∣4)] using hh'
  have hn := Nat.mod_lt n (by decide : 0<2)
  by_cases hz : n%2=0
  · refine ⟨address true,(anchor_iff he C epsilon (address true) v).mpr ?_,?_⟩
    · have hh := hc (address true)
      simp only [code,address,ite_true]
      cases epsilon <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod] at * <;> omega
    · intro a' ha'
      have hh := (anchor_iff he C epsilon a' v).mp ha'
      have hm := hc a'
      rw [address_eq a']
      cases ha : a' ⟨0,by decide⟩
      · simp only [code,ha] at hh
        cases epsilon <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod] at * <;> omega
      · rfl
  · refine ⟨address false,(anchor_iff he C epsilon (address false) v).mpr ?_,?_⟩
    · have hh := hc (address false)
      simp only [code,address]
      cases epsilon <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod] at * <;> omega
    · intro a' ha'
      have hh := (anchor_iff he C epsilon a' v).mp ha'
      have hm := hc a'
      rw [address_eq a']
      cases ha : a' ⟨0,by decide⟩
      · rfl
      · simp only [code,ha,ite_true] at hh
        cases epsilon <;> simp only [Bool.false_eq_true,ite_true,ite_false,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod] at * <;> omega

end Actual
#print axioms unique_anchor_owner
#print axioms unique_baseline_owner
#print axioms baseline_iff
#print axioms anchor_iff
end ErdePaths.QuarterPhysicalIncidence
