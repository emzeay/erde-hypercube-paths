import ErdePaths.QuarterProfileOrigins
import ErdePaths.SourceCodeOrigins

namespace ErdePaths.QuarterSourceOrigins
open SourceClock SourceProfile HierarchicalDecode SquareLift QuarterProfileOrigins

/-- The actual four phases are precisely the reserved-one dense source code. -/
theorem dense_code (epsilon : Bool) (a : Address 1) :
    (DenseSourceMarks.code 1 (by decide) epsilon a).val=QuarterProfileOrigins.code epsilon a := by
  let x : Vertex 2 := ⟨QuarterProfileOrigins.code epsilon a,QuarterProfileOrigins.code_lt epsilon a⟩
  have hx : x=DenseSourceMarks.code 1 (by decide) epsilon a := by
    apply (DenseSourceMarks.eq_code_iff 1 (by decide) epsilon a x).mpr
    constructor
    · intro i
      have hi : i=⟨0,by decide⟩ := by apply Fin.ext; have := i.isLt; omega
      subst i
      simp only [sparsePosition,show 0<1 by decide,ite_true]
      change (QuarterProfileOrigins.code epsilon a).testBit 0=a ⟨0,by decide⟩
      unfold QuarterProfileOrigins.code
      split <;> cases epsilon <;> simp_all
    · change (QuarterProfileOrigins.code epsilon a).testBit 1=epsilon
      unfold QuarterProfileOrigins.code
      split <;> cases epsilon <;> decide
  exact (congrArg Fin.val hx).symm

/-- Genuine source origin Data at k=1,h=0. Shifted profiles remove the
positive-upper-depth assumption rather than prescribing arbitrary endpoints. -/
noncomputable def data {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (a : Address 1) : SourceCodeOrigins.Data (u:=1) he C 1 0 1 (by decide)
      (QuarterProfileOrigins.selectors he) (QuarterProfileOrigins.odd he) a where
  arcFalse:=QuarterProfileOrigins.arc he C false a
  arcTrue:=QuarterProfileOrigins.arc he C true a
  start_equal:=QuarterProfileOrigins.same_start he C a
  end_equal:=QuarterProfileOrigins.same_end he C a
  false_code:=(QuarterProfileOrigins.origin_code he C false a).trans (dense_code false a).symm
  true_code:=(QuarterProfileOrigins.origin_code he C true a).trans (dense_code true a).symm

#print axioms data
#print axioms dense_code
end ErdePaths.QuarterSourceOrigins
