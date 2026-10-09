import ErdePaths.AACMarkIntervals

namespace ErdePaths.AACIntervalSplit
open SquareLift AACTransition AACFine AACFineClock AACFineGeometry AACMarkIntervals

/-- Every marked prefix level is attained at its unique actual mark. -/
theorem prefix_level_exists {E : Nat} (S : Fin E→Bool) (n : Nat) (hn : n≤E)
    (j : Nat) (hj : j<Profile.prefixCount S n) :
    ∃i : Fin E, i.val<n ∧ S i=true ∧ Profile.prefixCount S (i.val+1)=j+1 := by
  induction n with
  | zero => simp only [Profile.prefixCount] at hj; omega
  | succ n ih =>
    have hn' : n<E := by omega
    by_cases hj' : j<Profile.prefixCount S n
    · obtain ⟨i,hi,hs,hp⟩ := ih (by omega) hj'
      exact ⟨i,by omega,hs,hp⟩
    · have he : Profile.prefixCount S (n+1)=Profile.prefixCount S n+(S ⟨n,hn'⟩).toNat := by
        simp only [Profile.prefixCount,Profile.indicator,dite_eq_left hn']
      have hb := Bool.toNat_le (S ⟨n,hn'⟩)
      have hje : j=Profile.prefixCount S n := by omega
      have hs : S ⟨n,hn'⟩=true := by
        cases hh : S ⟨n,hn'⟩ <;> simp only [hh,Bool.toNat_false,Bool.toNat_true] at he
        · omega
        · rfl
      exact ⟨⟨n,hn'⟩,Nat.lt_succ_self n,hs,by rw [he,hs,hje]; rfl⟩

theorem prefix_mono {E : Nat} (S : Fin E→Bool) {a b : Nat} (h : a≤b) :
    Profile.prefixCount S a≤Profile.prefixCount S b := by
  induction b with
  | zero =>
    have ha : a=0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases ha : a≤b
    · have hi := ih ha
      simp only [Profile.prefixCount]
      omega
    · have he : a=b+1 := by omega
      subst a
      exact Nat.le_refl _

theorem marked_level_unique {E : Nat} (S : Fin E→Bool) (i k : Fin E)
    (hi : S i=true) (hk : S k=true)
    (he : Profile.prefixCount S (i.val+1)=Profile.prefixCount S (k.val+1)) : i=k := by
  have step (a : Fin E) (ha : S a=true) :
      Profile.prefixCount S (a.val+1)=Profile.prefixCount S a.val+1 := by
    simp only [Profile.prefixCount,Profile.indicator,dite_eq_left a.isLt,ha,Bool.toNat_true]
  have hn : i.val=k.val := by
    by_cases hl : i.val<k.val
    · have hm := prefix_mono S (show i.val+1≤k.val by omega)
      have hs := step k hk
      omega
    · by_cases hl' : k.val<i.val
      · have hm := prefix_mono S (show k.val+1≤i.val by omega)
        have hs := step i hi
        omega
      · omega
  exact Fin.ext hn

noncomputable def markIndex {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) : Fin E :=
  Classical.choose (prefix_level_exists S E (Nat.le_refl _) j.val j.isLt)

theorem markIndex_spec {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) :
    S (markIndex S j)=true ∧ Profile.prefixCount S ((markIndex S j).val+1)=j.val+1 :=
  (Classical.choose_spec (prefix_level_exists S E (Nat.le_refl _) j.val j.isLt)).2

/-- Literal chronological interiors of each color run. -/
def interiorPositions {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) : List (Fin E) :=
  (List.finRange E).filter (fun n => !S n && decide (Profile.prefixCount S (n.val+1)=j.val+1))

theorem mem_interiorPositions {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) (n : Fin E) :
    n∈interiorPositions S j ↔ S n=false ∧ Profile.prefixCount S (n.val+1)=j.val+1 := by
  simp only [interiorPositions,List.mem_filter,List.mem_finRange,true_and,Bool.and_eq_true,
    Bool.not_eq_true',decide_eq_true_eq]

theorem interiorPositions_nodup {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) :
    (interiorPositions S j).Nodup := (List.nodup_finRange E).filter _

theorem marked_level_before {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) :
    Profile.prefixCount S (markIndex S j).val=j.val := by
  have hj := markIndex_spec S j
  have hs : Profile.prefixCount S ((markIndex S j).val+1)=
      Profile.prefixCount S (markIndex S j).val+1 := by
    simp only [Profile.prefixCount,Profile.indicator,dite_eq_left (markIndex S j).isLt,hj.1,Bool.toNat_true]
  omega

theorem markIndex_order {E : Nat} (S : Fin E→Bool) (j k : Fin (Profile.cardinality S))
    (hj : j.val<k.val) : (markIndex S j).val<(markIndex S k).val := by
  have hs := markIndex_spec S j
  have ht := markIndex_spec S k
  by_cases hn : (markIndex S j).val<(markIndex S k).val
  · exact hn
  have hm := prefix_mono S (show (markIndex S k).val+1≤(markIndex S j).val+1 by omega)
  omega

/-- Run ownership exists for every original clock position after cutting at a
mark, including marks and interiors. -/
noncomputable def runIndex {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) : Fin (Profile.cardinality S) :=
  ⟨Profile.prefixCount S (n.val+1)-1,by
    have hfirst : Profile.prefixCount S 1=1 := by
      simp only [Profile.prefixCount,Profile.indicator,dite_eq_left hE,hzero,Bool.toNat_true,Nat.zero_add]
    have hlo := prefix_mono S (show 1≤n.val+1 by omega)
    have hup := prefix_mono S (show n.val+1≤E by have := n.isLt; omega)
    unfold Profile.cardinality
    omega⟩

theorem runIndex_spec {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) : Profile.prefixCount S (n.val+1)=(runIndex hE S hzero n).val+1 := by
  have hfirst : Profile.prefixCount S 1=1 := by
    simp only [Profile.prefixCount,Profile.indicator,dite_eq_left hE,hzero,Bool.toNat_true,Nat.zero_add]
  have hlo := prefix_mono S (show 1≤n.val+1 by omega)
  simp only [runIndex]
  omega

theorem runIndex_mark {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) (hn : S n=true) : markIndex S (runIndex hE S hzero n)=n := by
  have hj := markIndex_spec S (runIndex hE S hzero n)
  exact marked_level_unique S _ n hj.1 hn (hj.2.trans (runIndex_spec hE S hzero n).symm)

theorem runIndex_interior {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) (hn : S n=false) : n∈interiorPositions S (runIndex hE S hzero n) :=
  (mem_interiorPositions S _ n).mpr ⟨hn,runIndex_spec hE S hzero n⟩

/-- The filtered interior lies strictly after its own mark and before every
later mark. Thus it is the chronological gap, not an arbitrary fiber subset. -/
theorem interior_gap_bounds {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S))
    (n : Fin E) (hn : n∈interiorPositions S j) :
    (markIndex S j).val<n.val ∧
      ∀k : Fin (Profile.cardinality S), j.val<k.val → n.val<(markIndex S k).val := by
  have hp := (mem_interiorPositions S j n).mp hn
  have hj := markIndex_spec S j
  have hbefore := marked_level_before S j
  constructor
  · by_cases hh : (markIndex S j).val<n.val
    · exact hh
    have hle : n.val≤(markIndex S j).val := by omega
    by_cases he : n=markIndex S j
    · rw [he,hj.1] at hp
      exact Bool.noConfusion hp.1
    · have hl : n.val+1≤(markIndex S j).val := by
        have hv : n.val≠(markIndex S j).val := fun hh => he (Fin.ext hh)
        omega
      have hm := prefix_mono S hl
      omega
  · intro k hk
    by_cases hh : n.val<(markIndex S k).val
    · exact hh
    have hm := prefix_mono S (show (markIndex S k).val+1≤n.val+1 by omega)
    have hs := markIndex_spec S k
    omega

/-- Exact characterization of every consecutive gap, including the final
gap from the last mark to the cyclic cut E. -/
theorem interior_gap_iff {E : Nat} (S : Fin E→Bool) (j : Fin (Profile.cardinality S)) (n : Fin E) :
    n∈interiorPositions S j ↔ (markIndex S j).val<n.val ∧
      ∀k : Fin (Profile.cardinality S), j.val<k.val → n.val<(markIndex S k).val := by
  constructor
  · exact interior_gap_bounds S j n
  · rintro ⟨hlo,hhi⟩
    have hmark := markIndex_spec S j
    have hlow := prefix_mono S (show (markIndex S j).val+1≤n.val+1 by omega)
    have hup : Profile.prefixCount S (n.val+1)≤j.val+1 := by
      by_cases hn : j.val+1<Profile.cardinality S
      · let k : Fin (Profile.cardinality S) := ⟨j.val+1,hn⟩
        have hk := hhi k (by simp only [k]; omega)
        have hpre : Profile.prefixCount S (markIndex S k).val=j.val+1 := marked_level_before S k
        have hm := prefix_mono S (show n.val+1≤(markIndex S k).val by omega)
        omega
      · have hmax := prefix_mono S (show n.val+1≤E by have := n.isLt; omega)
        have hj := j.isLt
        unfold Profile.cardinality at hj hn
        omega
    have he : Profile.prefixCount S (n.val+1)=j.val+1 := by omega
    have hs : S n=false := by
      cases ht : S n
      · rfl
      · have hi := marked_level_unique S n (markIndex S j) ht hmark.1 (he.trans hmark.2.symm)
        have hv := congrArg Fin.val hi
        omega
    exact (mem_interiorPositions S j n).mpr ⟨hs,he⟩

abbrev InteriorIndex {E : Nat} (S : Fin E→Bool) :=
  (j : Fin (Profile.cardinality S)) × Fin (interiorPositions S j).length

def interiorIndex {E : Nat} (S : Fin E→Bool) (o : InteriorIndex S) : Fin E :=
  (interiorPositions S o.1)[o.2]

theorem interiorIndex_spec {E : Nat} (S : Fin E→Bool) (o : InteriorIndex S) :
    S (interiorIndex S o)=false ∧
      Profile.prefixCount S ((interiorIndex S o).val+1)=o.1.val+1 :=
  (mem_interiorPositions S o.1 _).mp (List.getElem_mem o.2.isLt)

theorem interiorIndex_injective {E : Nat} (S : Fin E→Bool) :
    Function.Injective (interiorIndex S) := by
  intro o p he
  have ho := interiorIndex_spec S o
  have hp := interiorIndex_spec S p
  have hj : o.1=p.1 := Fin.ext (by rw [he] at ho; omega)
  rcases o with ⟨j,a⟩
  rcases p with ⟨k,b⟩
  simp only at hj
  subst k
  have hab : a=b := Fin.ext ((interiorPositions_nodup S j).eq_of_getElem_eq a.isLt b.isLt he)
  subst b
  rfl

theorem interior_complete {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) (hn : S n=false) : ∃o : InteriorIndex S, interiorIndex S o=n := by
  have hm := runIndex_interior hE S hzero n hn
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hm
  exact ⟨⟨runIndex hE S hzero n,⟨k,hk⟩⟩,he⟩

theorem mark_complete {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (n : Fin E) (hn : S n=true) : ∃j, markIndex S j=n :=
  ⟨runIndex hE S hzero n,runIndex_mark hE S hzero n hn⟩

/-- The actual source cut is the first chronological mark. -/
theorem markIndex_zero {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hzero : S ⟨0,hE⟩=true)
    (j : Fin (Profile.cardinality S)) (hj : j.val=0) : markIndex S j=⟨0,hE⟩ := by
  have hs := markIndex_spec S j
  apply marked_level_unique S _ ⟨0,hE⟩ hs.1 hzero
  simp only [Profile.prefixCount,Profile.indicator,dite_eq_left hE,hzero,Bool.toNat_true,Nat.zero_add,hj] at hs ⊢
  exact hs.2

/-- Cumulative ranks agree exactly with the actual interior ordinal. -/
theorem interior_run_rank {E : Nat} (hE : 0<E) (color : Fin E→Bool)
    (hcut : cyclicFlag hE color ⟨0,hE⟩=true) (o : InteriorIndex (cyclicFlag hE color)) :
    changeRank (fun n => color ⟨n%E,Nat.mod_lt _ hE⟩)
      (interiorIndex (cyclicFlag hE color) o).val=o.1.val := by
  have hi := interiorIndex_spec (cyclicFlag hE color) o
  have hr := rank_prefix_flags hE color (interiorIndex (cyclicFlag hE color) o).val
    (interiorIndex (cyclicFlag hE color) o).isLt
  rw [hcut,Bool.toNat_true,hi.2] at hr
  omega

/-- Cardinality of the true mark flag equals the total cyclic change count
when the word has been cut at a genuine mark. -/
theorem cardinality_changeRank {E : Nat} (hE : 0<E) (color : Fin E→Bool)
    (hcut : cyclicFlag hE color ⟨0,hE⟩=true) :
    Profile.cardinality (cyclicFlag hE color)=
      changeRank (fun n => color ⟨n%E,Nat.mod_lt _ hE⟩) E := by
  let c : Nat→Bool := fun n => color ⟨n%E,Nat.mod_lt _ hE⟩
  have hlast : E-1<E := by omega
  have he : E-1+1=E := by omega
  have hp : predecessor hE (⟨0,hE⟩ : Fin E)=⟨E-1,hlast⟩ := by
    apply Fin.ext
    simp only [predecessor,Nat.add_zero,Nat.mod_eq_of_lt hlast]
  have hc : c (E-1)≠c E := by
    simp only [cyclicFlag,hp,decide_eq_true_eq] at hcut
    simpa only [c,Nat.mod_eq_of_lt hlast,Nat.mod_self] using hcut
  have hr := rank_prefix_flags hE color (E-1) hlast
  rw [hcut,Bool.toNat_true,he] at hr
  change Profile.prefixCount (cyclicFlag hE color) E=changeRank c E
  have hn : changeRank c E=changeRank c (E-1)+1 := by
    calc
      changeRank c E=changeRank c (E-1+1) := congrArg (changeRank c) he.symm
      _=changeRank c (E-1)+1 := by
        rw [changeRank,ite_eq_right (by simpa only [he] using hc)]
  rw [hn]
  exact hr.symm

theorem split_count_even {E : Nat} (hE : 0<E) (color : Fin E→Bool)
    (hcut : cyclicFlag hE color ⟨0,hE⟩=true) :
    Profile.cardinality (cyclicFlag hE color)%2=0 := by
  rw [cardinality_changeRank hE color hcut]
  exact cyclic_changeRank_even hE color

/-- A finite colored cyclic traversal, cut at an actual mark, supplies the
literal geometric interval data. The interiors are ordered filters of the
original word, not chosen output vertices. -/
noncomputable def split {V : Type} {E : Nat} (hE : 0<E) (vertex : Fin E→V) (color : Fin E→Bool)
    (hcut : cyclicFlag hE color ⟨0,hE⟩=true)
    (hmark : ∀n m, cyclicFlag hE color n=true → vertex n=vertex m → n=m)
    (hcollision : ∀n m, vertex n=vertex m → n=m ∨ color n≠color m) :
    AACUnfold.Intervals V (Profile.cardinality (cyclicFlag hE color)) where
  interior j := (interiorPositions (cyclicFlag hE color) j).length
  mark j := vertex (markIndex (cyclicFlag hE color) j)
  mark_injective := by
    intro j k he
    have hj := markIndex_spec (cyclicFlag hE color) j
    have hk := markIndex_spec (cyclicFlag hE color) k
    have hn := hmark _ _ hj.1 he
    apply Fin.ext
    rw [hn] at hj
    omega
  physical o := vertex (interiorIndex (cyclicFlag hE color) o)
  mark_exclusion := by
    intro o j he
    have ho := interiorIndex_spec (cyclicFlag hE color) o
    have hj := markIndex_spec (cyclicFlag hE color) j
    have hn := hmark _ _ hj.1 he.symm
    rw [hn] at hj
    rw [ho.1] at hj
    exact Bool.noConfusion hj.1
  collision := by
    intro o p he
    rcases hcollision _ _ he with hn|hc
    · exact Or.inl (interiorIndex_injective (cyclicFlag hE color) hn)
    · right
      let c : Nat→Bool := fun n => color ⟨n%E,Nat.mod_lt _ hE⟩
      have ho := interiorIndex_spec (cyclicFlag hE color) o
      have hp := interiorIndex_spec (cyclicFlag hE color) p
      have hro := rank_prefix_flags hE color (interiorIndex (cyclicFlag hE color) o).val
        (interiorIndex (cyclicFlag hE color) o).isLt
      have hrp := rank_prefix_flags hE color (interiorIndex (cyclicFlag hE color) p).val
        (interiorIndex (cyclicFlag hE color) p).isLt
      rw [hcut,Bool.toNat_true,ho.2] at hro
      rw [hcut,Bool.toNat_true,hp.2] at hrp
      have hro' : changeRank c (interiorIndex (cyclicFlag hE color) o).val=o.1.val  := by dsimp only [c]; omega
      have hrp' : changeRank c (interiorIndex (cyclicFlag hE color) p).val=p.1.val := by dsimp only [c]; omega
      have hcp : c (interiorIndex (cyclicFlag hE color) o).val≠
          c (interiorIndex (cyclicFlag hE color) p).val := by
        simpa only [c,Nat.mod_eq_of_lt (interiorIndex (cyclicFlag hE color) o).isLt,
          Nat.mod_eq_of_lt (interiorIndex (cyclicFlag hE color) p).isLt,Fin.eta] using hc
      simpa only [hro',hrp'] using changeRank_parity hcp

theorem forward_predecessor {E : Nat} (hE : 0<E) (cut n : Fin E) :
    forward hE cut (predecessor hE n)=predecessor hE (forward hE cut n) := by
  have hs := HamiltonNormalize.forward_successor hE cut (predecessor hE n)
  rw [successor_predecessor] at hs
  have hp := congrArg (predecessor hE) hs
  simpa only [predecessor_successor] using hp.symm

/-- Same-color collisions are ruled out by the actual fine geometry, before
cyclic splitting is performed. -/
theorem numeric_color_collision {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (fineLabel hK hA hB C hE))
    (hcoarse : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (z : Fin A) (hz : 0<z.val) (n m : Fin E)
    (he : fineVertex hK hA hB C hE n=fineVertex hK hA hB C hE m) :
    n=m ∨ numericColor hK hA hB C hE z n≠numericColor hK hA hB C hE z m := by
  rcases fine_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hlabel hcoarse n m he with hn|⟨g,hg,hc⟩
  · exact Or.inl hn
  · right
    rw [numeric_grid_color hK hA hB hb C hE z hz n g hg,
      numeric_grid_color hK hA hB hb C hE z hz m g (he.symm.trans hg)]
    exact hc

/-- Concrete interval data for the actual fine Euler word, cut at a specified
genuine turn-agreement mark. All generic split premises are derived here. -/
noncomputable def fineIntervals {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (fineLabel hK hA hB C hE))
    (hcoarse : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (z : Fin A) (hz : 0<z.val) (cut : Fin E)
    (hcut : IsMark hK turns z (fineVertex hK hA hB C hE cut)) :
    AACUnfold.Intervals (Fine K A B)
      (Profile.cardinality (cyclicFlag hpos (fun n => numericColor hK hA hB C hE z (forward hpos cut n)))) := by
  let vertex := fun n => fineVertex hK hA hB C hE (forward hpos cut n)
  let color := fun n => numericColor hK hA hB C hE z (forward hpos cut n)
  have mark_iff (n : Fin E) : cyclicFlag hpos color n=true ↔
      IsMark hK turns z (vertex n) := by
    have hc := numeric_change_iff hK hA hB hb C hE hpos z hz (predecessor hpos (forward hpos cut n))
    rw [successor_predecessor] at hc
    simpa only [cyclicFlag,color,vertex,forward_predecessor,decide_eq_true_eq] using hc
  have hc : cyclicFlag hpos color ⟨0,hpos⟩=true :=
    (mark_iff _).mpr (by simpa only [vertex,forward_zero] using hcut)
  apply split hpos vertex color hc
  · intro n m hn he
    have hmark := (mark_iff n).mp hn
    have hi := nonGrid_clock_collision hK hA hB h3 hB3 C hE hpos hE2 hlabel
      (forward hpos cut n) (forward hpos cut m) (mark_nonGrid hK hA turns z hz _ hmark) he
    exact forward_injective hpos cut hi
  · intro n m he
    rcases numeric_color_collision hK hA hB h3 hB3 hb C hE hpos hE2 hlabel hcoarse z hz
      (forward hpos cut n) (forward hpos cut m) he with hn|hc
    · exact Or.inl (forward_injective hpos cut hn)
    · exact Or.inr hc

/-- A surviving literal agreement supplies the cut automatically through the
constructed fine edge cover. No interval-existence input is required. -/
theorem fineIntervals_exists {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A := A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hlabel : Function.Injective (fineLabel hK hA hB C hE))
    (hsur : Function.Surjective (fineLabel hK hA hB C hE))
    (hcoarse : Function.Injective (fun n => AACEdge.incoming hK hB (C.point n)))
    (z : Fin A) (hz : 0<z.val) (i : Fin K) (j : Fin B)
    (hag : turns (i,j)=turns (successor hK i,j)) :
    ∃q, Nonempty (AACUnfold.Intervals (Fine K A B) q) := by
  obtain ⟨cut,hcut,hu⟩ := internal_clock_owner hK hA hB h3 hB3 C hE hpos hE2 hlabel hsur i z hz j
  have hm : IsMark hK turns z (fineVertex hK hA hB C hE cut) :=
    ⟨i,j,hcut,hag⟩
  exact ⟨_,⟨fineIntervals hK hA hB h3 hB3 hb C hE hpos hE2 hlabel hcoarse z hz cut hm⟩⟩

/-- Fully constructed interval data for every balanced turn pattern with its
surviving zero-column agreement. Euler existence and label ownership are
derived internally from the B-1 chain construction. -/
theorem balanced_fineIntervals_exists {K A B : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (heven : B%2=0)
    (t : Fin K→Bool) (hbalanced : BalancedTurns t) (ht0 : t ⟨0,hK⟩=false)
    (ht1 : t (successor hK ⟨0,hK⟩)=false) (z : Fin A) (hz : 0<z.val) :
    ∃q, Nonempty (AACUnfold.Intervals (Fine K A B) q) := by
  obtain ⟨C,⟨hinj,hsur⟩,hstep⟩ := AACOwnership.coarse_euler hK hB t hbalanced ht0
  let hN : 0<B*(2*K) := Nat.mul_pos hB (by omega)
  have hout : Function.Injective (fun n => AACEdge.incoming hK hB (C.point (successor hN n))) := by
    intro n m he
    have hn := hinj he
    have hp := congrArg (predecessor hN) hn
    simpa only [predecessor_successor] using hp
  have hsout : Function.Surjective (fun n => AACEdge.incoming hK hB (C.point (successor hN n))) := by
    intro e
    obtain ⟨n,hn⟩ := hsur e
    exact ⟨predecessor hN n,by simpa only [successor_predecessor] using hn⟩
  have hfine := expanded_label_injective hK hA hB C hout
  have hsfine := expanded_label_surjective hK hA hB C hsout
  let hE := indexList_length hK hA hB C hfine hsfine
  have hnum : Function.Injective (fineLabel hK hA hB C hE) := by
    intro n m he
    exact exactPosition_injective C hE (hfine he)
  have hsnum : Function.Surjective (fineLabel hK hA hB C hE) := by
    intro e
    obtain ⟨p,hp⟩ := hsfine e
    obtain ⟨n,hn⟩ := exactPosition_surjective C hE p
    exact ⟨n,by change expandedLabel hK hA hB C (exactPosition C hE n)=e; rw [hn,hp]⟩
  let j : Fin B := ⟨B-1,by omega⟩
  have hag : AACInduction.turnsAfter hK t (B-1) (⟨0,hK⟩,j)=
      AACInduction.turnsAfter hK t (B-1) (successor hK ⟨0,hK⟩,j) := by
    simp only [AACInduction.turnsAfter,j,Nat.lt_irrefl,and_false,ite_false,ht0,ht1]
  let hpos : 0<K*B*(A+1) := Nat.mul_pos (Nat.mul_pos hK hB) (by omega)
  have hlen : 2≤K*B*(A+1) := by
    have hkb : B≤K*B := by
      calc B=1*B := by omega
           _≤K*B := Nat.mul_le_mul_right B (by omega)
    have hmul : K*B≤K*B*(A+1) := by
      calc K*B=K*B*1 := by omega
           _≤K*B*(A+1) := Nat.mul_le_mul_left (K*B) (by omega)
    omega
  exact fineIntervals_exists hK hA hB h3 hB3 heven C hE hpos hlen hnum hsnum hinj z hz ⟨0,hK⟩ j hag

#print axioms balanced_fineIntervals_exists
#print axioms fineIntervals
#print axioms fineIntervals_exists
#print axioms split
end ErdePaths.AACIntervalSplit
