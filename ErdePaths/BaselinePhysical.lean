import ErdePaths.AACResidueBridge
import ErdePaths.BaselineResidues

namespace ErdePaths.BaselinePhysical
open SourceClock SquareLift OrientedClock AACResidueBridge

/-- Actual positive within-cell threshold as a full clock index. -/
def threshold {K A : Nat} (hK : 0<K) (z : Fin A) : Fin (K*A) :=
  ⟨z.val,by
    have ha := Nat.mul_le_mul_right A (show 1≤K by omega)
    simp only [Nat.one_mul] at ha
    have := z.isLt
    omega⟩

private theorem residue_bound {A L : Nat} (_hA : 0<A) (u : Fin L) (z : Fin A) :
    A*u.val+z.val<A*L := by
  have hm := Nat.mul_le_mul_left A (show u.val+1≤L by have := u.isLt; omega)
  rw [Nat.mul_add,Nat.mul_one] at hm
  have := z.isLt
  omega

/-- The actual baseline mark at any physical first-axis vertex and row is
exactly the union of its b counted signed source residue classes. The origin
uses a real endpoint occurrence, not a canonical phase representative. -/
theorem anti_physical_classes {U : Type} {K A B L b : Nat}
    (hK : 0<K) (hA : 0<A) (hL : 0<L) (hd : 2*L∣K)
    (hb : b<L) (he : L%2=0) (ho : b%2=1)
    (C : ClockData U (K*A)) (endpoint : Fin (K*A)) (code : Fin (A*L))
    (hcode : endpoint.val%(A*L)=code.val) (z : Fin A) (epsilon : Bool)
    (v : U) (j : Fin B) :
    AACMarkIntervals.IsMark hK
      (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.anti (L:=L) b) w.1) z
      (((clock (Nat.mul_pos hK hA) C
        (index (Nat.mul_pos hK hA) endpoint (!epsilon) (threshold hK z)) epsilon).position v),j) ↔
      ∃u : Fin b, shiftedResidue (A*L)
        (SourceStability.signedOffset (A*L) A u.val (!epsilon)) (C.position v).val=code.val := by
  have hdiv : A*L∣K*A := by
    have hl : L∣K := Nat.dvd_trans (Nat.dvd_mul_left L 2) hd
    simpa only [Nat.mul_comm K A] using Nat.mul_dvd_mul_left A hl
  rw [BaselineResidues.anti_marks_iff hK hA hL hd hb he ho]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,?_⟩
    have hh := physical_spaced_residue_iff (Nat.mul_pos hK hA) (Nat.mul_pos hA hL)
      hdiv C endpoint (threshold hK z) A u.val epsilon v
    rw [hcode] at hh
    apply hh.mpr
    have hbound := residue_bound hA (⟨u.val,by have := u.isLt; omega⟩ : Fin L) z
    simpa only [threshold,Nat.mod_eq_of_lt hbound] using hu
  · rintro ⟨u,hu⟩
    refine ⟨u,?_⟩
    have hh := physical_spaced_residue_iff (Nat.mul_pos hK hA) (Nat.mul_pos hA hL)
      hdiv C endpoint (threshold hK z) A u.val epsilon v
    rw [hcode] at hh
    have hbound := residue_bound hA (⟨u.val,by have := u.isLt; omega⟩ : Fin L) z
    simpa only [threshold,Nat.mod_eq_of_lt hbound] using hh.mp hu

/-- Individual actual coordinate/source class equivalence for any period. -/
theorem class_incidence {U : Type} {K A L : Nat}
    (hK : 0<K) (hA : 0<A) (hL : 0<L) (hd : L∣K)
    (C : ClockData U (K*A)) (endpoint : Fin (K*A)) (code : Fin (A*L))
    (hcode : endpoint.val%(A*L)=code.val) (z : Fin A) (epsilon : Bool)
    (v : U) (u : Fin L) :
    ((clock (Nat.mul_pos hK hA) C
      (index (Nat.mul_pos hK hA) endpoint (!epsilon) (threshold hK z)) epsilon).position v).val%(A*L)=
        A*u.val+z.val ↔
      shiftedResidue (A*L) (SourceStability.signedOffset (A*L) A u.val (!epsilon))
        (C.position v).val=code.val := by
  have hdiv : A*L∣K*A := by
    simpa only [Nat.mul_comm K A] using Nat.mul_dvd_mul_left A hd
  have hh := physical_spaced_residue_iff (Nat.mul_pos hK hA) (Nat.mul_pos hA hL)
    hdiv C endpoint (threshold hK z) A u.val epsilon v
  rw [hcode] at hh
  have hbound := residue_bound hA u z
  simpa only [threshold,Nat.mod_eq_of_lt hbound] using hh.symm

/-- Every physical long-word baseline mark is exactly an eligible residue
other than the four bad coarse starts; this is the full union equivalence. -/
theorem long_physical_marks {U : Type} {K A B P : Nat}
    (hK : 0<K) (hA : 0<A) (hP : 8≤P) (hd : 2*P∣K)
    (C : ClockData U (K*A)) (endpoint : Fin (K*A)) (code : Fin (A*(2*P)))
    (hcode : endpoint.val%(A*(2*P))=code.val) (z : Fin A) (epsilon : Bool)
    (v : U) (j : Fin B) :
    AACMarkIntervals.IsMark hK
      (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1) z
      (((clock (Nat.mul_pos hK hA) C
        (index (Nat.mul_pos hK hA) endpoint (!epsilon) (threshold hK z)) epsilon).position v),j) ↔
      ∃u : Fin (2*P), ¬BaselineResidues.Bad P u.val ∧
        shiftedResidue (A*(2*P))
          (SourceStability.signedOffset (A*(2*P)) A u.val (!epsilon)) (C.position v).val=code.val := by
  rw [BaselineResidues.long_marks_iff hK hA hP hd]
  constructor
  · rintro ⟨u,hu,hx⟩
    exact ⟨u,hu,(class_incidence hK hA (by omega) hd C endpoint code hcode z epsilon v u).mp hx⟩
  · rintro ⟨u,hu,hx⟩
    exact ⟨u,hu,(class_incidence hK hA (by omega) hd C endpoint code hcode z epsilon v u).mpr hx⟩

/-- Literal threshold unmarks correspond exactly to the four bad source
classes. The threshold condition excludes all unrelated grid vertices. -/
theorem long_physical_unmarks {U : Type} {K A B P : Nat}
    (hK : 0<K) (hA : 0<A) (hP : 8≤P) (hd : 2*P∣K)
    (C : ClockData U (K*A)) (endpoint : Fin (K*A)) (code : Fin (A*(2*P)))
    (hcode : endpoint.val%(A*(2*P))=code.val) (z : Fin A) (epsilon : Bool)
    (v : U) (j : Fin B) :
    let G := clock (Nat.mul_pos hK hA) C
      (index (Nat.mul_pos hK hA) endpoint (!epsilon) (threshold hK z)) epsilon
    ((∃i : Fin K, G.position v=AnchoredEmbedding.positionEncode i z) ∧
      ¬AACMarkIntervals.IsMark hK
        (fun w=>TurnPatterns.repeated (by omega) (TurnPatterns.long (P:=P)) w.1) z (G.position v,j)) ↔
      ∃u : Fin (2*P), BaselineResidues.Bad P u.val ∧
        shiftedResidue (A*(2*P))
          (SourceStability.signedOffset (A*(2*P)) A u.val (!epsilon)) (C.position v).val=code.val := by
  dsimp only
  rw [BaselineResidues.long_unmark_iff hK hA hP hd]
  constructor
  · rintro ⟨u,hu,hx⟩
    exact ⟨u,hu,(class_incidence hK hA (by omega) hd C endpoint code hcode z epsilon v u).mp hx⟩
  · rintro ⟨u,hu,hx⟩
    exact ⟨u,hu,(class_incidence hK hA (by omega) hd C endpoint code hcode z epsilon v u).mpr hx⟩

#print axioms class_incidence
#print axioms long_physical_marks
#print axioms long_physical_unmarks
#print axioms anti_physical_classes
end ErdePaths.BaselinePhysical
