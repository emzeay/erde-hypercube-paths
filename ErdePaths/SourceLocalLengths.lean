import ErdePaths.SourceLocalFold
import ErdePaths.UniformFoldLengths

namespace ErdePaths.SourceLocalLengths
set_option warn.classDefReducibility false
open SourceLocalFold AACMarkIntervals
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Every actual ordinary host has the exact same derived chronological
mark count; no word-size equality is an input. -/
theorem word_length (I : Input) (n : I.Index) :
    (I.marks.word n).length=
      I.b*(2^(I.e*2^(I.a+I.h+1)-I.r)/2^(I.a+I.h+1-I.r))*I.B := by
  rw [←I.flag_card n]
  exact AACPatternCardinality.source_anti_cardinality I.he I.a I.h I.r I.hr
    I.hB (by have := I.hB4; omega) I.evenB I.short I.odd I.z I.hz

/-- Literal numeric fold length, with actual marks already counted. -/
theorem fold_length (I : Input) (n : I.Index) {jR : Nat} (_hj : 0<jR) :
    I.length (jR:=jR) n=jR*(I.E+
      I.b*(2^(I.e*2^(I.a+I.h+1)-I.r)/2^(I.a+I.h+1-I.r))*I.B) := by
  unfold Input.length
  rw [AACFoldClock.length_eq I.epos (I.flag n) (I.cut_mark n) (I.qpos n),I.mark_card n,word_length]

/-- Uniform actual frontier expression when H and J have their genuine
Hamilton cube lengths. This does not assume a frontier decomposition. -/
theorem frontier_length (I : Input) (n : I.Index) (H j : Nat) (hj : 1≤j)
    (hB : I.B=2^H) :
    I.length (jR:=2^(j-1)) n=
      (2^(I.a+I.h+1)+2^(I.a+I.h+1-I.r)+I.b)*
        2^(I.e*2^(I.a+I.h+1)+H+j-(I.a+I.h+1)-1) := by
  rw [fold_length I n (Nat.two_pow_pos _)]
  unfold Input.E
  rw [hB]
  have hs : I.r+(I.a+I.h+1-I.r)=I.a+I.h+1 := by have := I.hr; omega
  have hr := SourceLengths.source_exponent_room I.he I.a I.h
  have hroom : I.r+(I.a+I.h+1-I.r)≤I.e*2^(I.a+I.h+1) := by omega
  have hh := UniformFoldLengths.ordinary (b:=I.b) (H:=H) hroom hj
  rw [hs] at hh
  exact hh

#print axioms word_length
#print axioms fold_length
#print axioms frontier_length
end ErdePaths.SourceLocalLengths
