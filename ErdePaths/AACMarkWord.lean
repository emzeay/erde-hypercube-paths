import ErdePaths.AACMarkIntervals

namespace ErdePaths.AACMarkWord
attribute [local instance] Classical.propDecidable
open AACTransition AACFine AACFineClock AACFineGeometry AACMarkIntervals

/-- Every actual geometric mark occurs in the chronological Euler mark word. -/
theorem mem_word_iff {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (hsur : Function.Surjective (fineLabel hK hA hB C hE))
    (z : Fin A) (hz : 0<z.val) (v : Fine K A B) :
    v∈markWord hK hA hB C hE hpos z ↔ IsMark hK turns z v := by
  constructor
  · intro hm
    obtain ⟨n,hn,he⟩ := List.mem_map.mp hm
    exact he ▸ (mem_markPositions hK hA hB hb C hE hpos z hz n).mp hn
  · intro hm
    obtain ⟨n,hn⟩ := fineVertex_surjective hK hA hB C hE hpos hsur v
    apply List.mem_map.mpr
    refine ⟨n,?_,hn⟩
    apply (mem_markPositions hK hA hB hb C hE hpos z hz n).mpr
    exact hn ▸ hm

/-- Physical word membership tests actual factor inverse coordinates. -/
theorem mem_physical_word_iff {U V : Type} {K A B N E : Nat}
    (hK : 0<K) (hA : 0<A) (hB : 0<B) (hb : B%2=0)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E)
    (hsur : Function.Surjective (fineLabel hK hA hB C hE))
    (z : Fin A) (hz : 0<z.val) (G : SourceClock.ClockData U (K*A))
    (H : SourceClock.ClockData V B) (v : U×V) :
    v∈(markWord hK hA hB C hE hpos z).map (physical G H) ↔
      IsMark hK turns z (G.position v.1,H.position v.2) := by
  constructor
  · intro hm
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    have hh : (G.position v.1,H.position v.2)=x := by
      rw [←he]
      simp only [physical,G.position_cycle,H.position_cycle]
    rw [hh]
    exact (mem_word_iff hK hA hB hb C hE hpos hsur z hz x).mp hx
  · intro hm
    refine List.mem_map.mpr ⟨(G.position v.1,H.position v.2),?_,?_⟩
    · exact (mem_word_iff hK hA hB hb C hE hpos hsur z hz _).mpr hm
    · simp only [physical,G.cycle_position,H.cycle_position]

/-- Actual chronological marks have 0/1 physical incidence, with all coarse
Euler repetitions removed by their proved degree-two uniqueness. -/
theorem physical_word_incidence {U V : Type} {K A B N E : Nat}
    (hK : 0<K) (hA : 0<A) (hB : 0<B) (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0)
    {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE))
    (hsur : Function.Surjective (fineLabel hK hA hB C hE))
    (z : Fin A) (hz : 0<z.val) (G : SourceClock.ClockData U (K*A))
    (H : SourceClock.ClockData V B) (v : U×V) :
    ((markWord hK hA hB C hE hpos z).map (physical G H)).countP (fun w=>decide (w=v))=
      if IsMark hK turns z (G.position v.1,H.position v.2) then 1 else 0 := by
  classical
  let W := (markWord hK hA hB C hE hpos z).map (physical G H)
  have hn : W.Nodup := by
    apply List.pairwise_map.mpr
    exact (markWord_nodup hK hA hB h3 hB3 hb C hE hpos hE2 hinj z hz).imp
      (fun hne he=>hne (physical_injective G H he))
  have hp : (fun w : U×V=>decide (w=v))=(fun w=>w==v) := by
    funext w
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq]
  rw [hp,←List.count_eq_countP]
  have hc := hn.count (a:=v)
  simpa only [W,mem_physical_word_iff hK hA hB hb C hE hpos hsur z hz G H v] using hc

#print axioms physical_word_incidence
end ErdePaths.AACMarkWord
