import ErdePaths.SingletonPhaseArc
import ErdePaths.SourceProfile

namespace ErdePaths.QuarterProfileOrigins
open SourceClock SourceProfile HierarchicalDecode SquareLift

def address (b : Bool) : Address 1 := fun _=>b

theorem address_eq (a : Address 1) : a=address (a ⟨0,by decide⟩) := by
  funext i
  have hi : i=⟨0,by decide⟩ := by apply Fin.ext; have := i.isLt; omega
  rw [hi]
  rfl

def code (epsilon : Bool) (a : Address 1) : Nat :=
  (if a ⟨0,by decide⟩ then 1 else 0)+2*(if epsilon then 1 else 0)

theorem code_lt (epsilon : Bool) (a : Address 1) : code epsilon a<4 := by
  unfold code
  cases a ⟨0,by decide⟩ <;> cases epsilon <;> decide

theorem code_injective (epsilon epsilon' : Bool) (a a' : Address 1)
    (h : code epsilon a=code epsilon' a') : epsilon=epsilon' ∧ a=a' := by
  rw [address_eq a,address_eq a'] at h ⊢
  cases ha : a ⟨0,by decide⟩ <;> cases hb : a' ⟨0,by decide⟩ <;>
    cases epsilon <;> cases epsilon' <;> simp_all [code,address]

theorem code_bijection (q : Fin 4) :
    ∃epsilon a, code epsilon a=q.val ∧
      ∀epsilon' a', code epsilon' a'=q.val→epsilon'=epsilon ∧ a'=a := by
  have hex : ∃epsilon a, code epsilon a=q.val := by
    have hq : q.val=0 ∨ q.val=1 ∨ q.val=2 ∨ q.val=3 := by have := q.isLt; omega
    rcases hq with hq|hq|hq|hq
    · exact ⟨false,address false,by simp [code,address,hq]⟩
    · exact ⟨false,address true,by simp [code,address,hq]⟩
    · exact ⟨true,address false,by simp [code,address,hq]⟩
    · exact ⟨true,address true,by simp [code,address,hq]⟩
  obtain ⟨epsilon,a,ha⟩ := hex
  exact ⟨epsilon,a,ha,fun epsilon' a' h=>code_injective epsilon' epsilon a' a (h.trans ha.symm)⟩

section Actual
variable {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))

def phase (a : Address 1) : Fin (2^(e*2^1)) :=
  ⟨if a ⟨0,by decide⟩ then 1 else 0,by
    have hp := SourceProfile.exponent_bound he 1
    have hN := Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤e*2^1 by omega)
    cases a ⟨0,by decide⟩ <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩

def selectors (a : Address 1) : Fin (2^(e*2^1))→Bool :=
  SingletonPhaseArc.selector (phase he a)

theorem odd (a : Address 1) : Profile.cardinality (selectors he a)%2=1 := by
  unfold selectors
  rw [SingletonPhaseArc.cardinality_one]

noncomputable def clock (epsilon : Bool) (a : Address 1) :=
  SourceProfile.clock he C 1 0 (selectors he) (odd he) epsilon a

theorem common_mod_four (epsilon epsilon' : Bool) (a a' : Address 1)
    (v : VertexPower V 1×VertexPower V 1) :
    ((clock he C epsilon a).position v).val%4=
      ((clock he C epsilon' a').position v).val%4 := by
  exact SourceProfile.lower_prefix_common he C 1 0 0 (by omega)
    (by simpa only [lengthPower] using Nat.pow_dvd_pow 2 he)
    (selectors he) (selectors he) (odd he) (odd he) epsilon epsilon' a a'
    (by intro i hi; omega) v

/-- Real singleton-profile twin arcs at the source bit's literal phase. -/
noncomputable def arc (epsilon : Bool) (a : Address 1) :
    PairedArc.DirectedArc (Nat.mul_pos (Nat.two_pow_pos (e*2^1)) (Nat.two_pow_pos (e*2^1)))
      (clock he C epsilon a) 2 :=
  SingletonPhaseArc.lifted (by have := SourceProfile.exponent_bound he 1; omega)
    (prefixClock C 1 a) (phase he a) epsilon

theorem same_start (a : Address 1) :
    (arc he C false a).vertex ⟨0,by decide⟩=(arc he C true a).vertex ⟨0,by decide⟩ := by
  rw [arc,arc,SingletonPhaseArc.lifted_start,SingletonPhaseArc.lifted_start]

theorem same_end (a : Address 1) :
    (arc he C false a).vertex ⟨2,by decide⟩=(arc he C true a).vertex ⟨2,by decide⟩ := by
  rw [arc,arc,SingletonPhaseArc.lifted_endpoint,SingletonPhaseArc.lifted_endpoint]

noncomputable def origin (epsilon : Bool) (a : Address 1) :
    Fin ((2^(e*2^1))*(2^(e*2^1))) :=
  (clock he C epsilon a).position ((arc he C epsilon a).vertex
    (if epsilon then ⟨2,by decide⟩ else ⟨0,by decide⟩))

theorem origin_code (epsilon : Bool) (a : Address 1) :
    (origin he C epsilon a).val%4=code epsilon a := by
  have hp : 1≤e*2^1 := by have := SourceProfile.exponent_bound he 1; omega
  have hd : 4∣2^(e*2^1) := by simpa only [show 2^2=4 by decide] using Nat.pow_dvd_pow 2 (show 2≤e*2^1 by omega)
  have hh := SingletonPhaseArc.lifted_phases hp hd (prefixClock C 1 a) (phase he a) epsilon
  cases epsilon
  · change _=code false a
    exact hh.1.trans (by
      change (if a ⟨0,by decide⟩ then 1 else 0)%4=(if a ⟨0,by decide⟩ then 1 else 0)
      split <;> decide)
  · exact hh.2.trans (by
      change ((if a ⟨0,by decide⟩ then 1 else 0)+2)%4=(if a ⟨0,by decide⟩ then 1 else 0)+2
      split <;> decide)

/-- All four actual clocks share a residue, and their literal origins exhaust
it exactly once. This is genuine physical ownership, not four supplied classes. -/
theorem unique_quarter_owner (v : VertexPower V 1×VertexPower V 1) :
    ∃epsilon a, ((clock he C epsilon a).position v).val%4=code epsilon a ∧
      ∀epsilon' a', ((clock he C epsilon' a').position v).val%4=code epsilon' a'→
        epsilon'=epsilon ∧ a'=a := by
  let q : Fin 4 := ⟨((clock he C false (address false)).position v).val%4,Nat.mod_lt _ (by decide)⟩
  obtain ⟨epsilon,a,ha,hu⟩ := code_bijection q
  have hc (epsilon' : Bool) (a' : Address 1) :
      ((clock he C epsilon' a').position v).val%4=q.val :=
    common_mod_four he C epsilon' false a' (address false) v
  refine ⟨epsilon,a,(hc epsilon a).trans ha.symm,?_⟩
  intro epsilon' a' h
  exact hu epsilon' a' (h.symm.trans (hc epsilon' a'))

end Actual
#print axioms unique_quarter_owner
#print axioms origin_code
end ErdePaths.QuarterProfileOrigins
