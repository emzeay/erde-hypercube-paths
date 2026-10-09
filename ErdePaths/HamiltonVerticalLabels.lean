import ErdePaths.HamiltonLedger

namespace ErdePaths.HamiltonVerticalLabels
open HamiltonScan HamiltonLedger

def Class {N k : Nat} (M : Matching N k) (s : Nat→Bool) (j : Nat) (b : Bool) : Prop :=
  M.kind j=.ordinary ∨
  (∃i, M.kind j=.lower i ∧ b=s (M.upper i)) ∨
  (∃i, M.kind j=.upper i ∧ b=!(s (M.upper i)))

/-- Exact vertical scan-label incidence, derived from actual selected-endpoint
lookup. This is uniform in the arbitrary scan state function. -/
theorem membership {N k : Nat} (M : Matching N k) (s : Nat→Bool) (j : Nat) (b : Bool) :
    (∃q, q∈middle N ∧ Label.vertical j b∈labels M s q) ↔ j∈middle N ∧ Class M s j b := by
  constructor
  · rintro ⟨q,hq,ha⟩
    have ho := labels_owner M s q (.vertical j b) ha
    cases hk : M.kind j with
    | ordinary =>
      simp only [labelOwner,hk] at ho
      rw [←ho] at hq
      exact ⟨hq,Or.inl hk⟩
    | lower i =>
      simp only [labelOwner,hk] at ho
      rw [←ho] at hq ha
      have hj := M.kind_lower j i hk
      have hne : j≠M.upper i := by rw [hj]; have := M.ordered i; omega
      have hb : b=s (M.upper i) := by
        simpa [labels,hk,hne] using ha
      exact ⟨hq,Or.inr (Or.inl ⟨i,hk,hb⟩)⟩
    | upper i =>
      simp only [labelOwner,hk] at ho
      rw [←ho] at ha
      have hj := M.kind_upper j i hk
      have hne : j≠M.lower i := by rw [hj]; have := M.ordered i; omega
      have hne' : M.upper i≠M.lower i := by have := M.ordered i; omega
      have hb : b=!(s (M.upper i)) := by
        simpa [labels,M.lower_kind,hj,hne'] using ha
      have hm : j∈middle N := by
        apply middle_mem.mpr
        rw [hj]
        have := M.lower_pos i
        have := M.ordered i
        exact ⟨by omega,M.upper_bound i⟩
      exact ⟨hm,Or.inr (Or.inr ⟨i,hk,hb⟩)⟩
  · rintro ⟨hj,hc⟩
    rcases hc with hc | ⟨i,hk,hb⟩ | ⟨i,hk,hb⟩
    · refine ⟨j,hj,?_⟩
      cases hs : s j <;> cases b <;> simp [labels,hc,hs]
    · refine ⟨j,hj,?_⟩
      simp [labels,hk,hb]
    · refine ⟨M.lower i,lower_middle M i,?_⟩
      have he := M.kind_upper j i hk
      simp [labels,M.lower_kind,he,hb]

#print axioms membership
end ErdePaths.HamiltonVerticalLabels
