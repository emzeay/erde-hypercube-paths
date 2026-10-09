import ErdePaths.AACIsolatedFork

namespace ErdePaths.AACIsolatedOpening
open SquareLift PairedLayers LayerPartition AACIntervalSplit AACFoldGeometry AACFoldOrder AACUnfold
open AACMarkIntervals AACFoldFork
attribute [local instance] Classical.propDecidable
variable {Y X : Type} {R : X→X→Prop} {χ : X→Bool} {r : Nat} {hr : 0<r}

/-- Actual chronological color inequality implies opposite interval ranks;
this applies to any literal first-mark cut, not just source Inputs. -/
theorem ordinal_parity {E : Nat} (hE : 0<E) (c : Fin E→Bool)
    (hcut : cyclicFlag hE c ⟨0,hE⟩=true)
    (o p : InteriorIndex (cyclicFlag hE c))
    (hc : c (interiorIndex (cyclicFlag hE c) o)≠c (interiorIndex (cyclicFlag hE c) p)) :
    o.1.val%2≠p.1.val%2 := by
  let w : Nat→Bool := fun k=>c ⟨k%E,Nat.mod_lt _ hE⟩
  have ho := interior_run_rank hE c hcut o
  have hp := interior_run_rank hE c hcut p
  have hh : w (interiorIndex (cyclicFlag hE c) o).val≠
      w (interiorIndex (cyclicFlag hE c) p).val := by
    simpa only [w,Nat.mod_eq_of_lt (interiorIndex (cyclicFlag hE c) o).isLt,
      Nat.mod_eq_of_lt (interiorIndex (cyclicFlag hE c) p).isLt,Fin.eta] using hc
  have hs := changeRank_parity hh
  change changeRank w (interiorIndex (cyclicFlag hE c) o).val=o.1.val at ho
  change changeRank w (interiorIndex (cyclicFlag hE c) p).val=p.1.val at hp
  rw [ho,hp] at hs
  exact hs

/-- Membership and exclusion in the actual numeric fold follow from actual
unique unmarked input occurrences and their chronological color inequality. -/
theorem opposite_owners {E : Nat} (hE : 0<E) (base : Fin E→Y) (c : Fin E→Bool)
    (hcut : cyclicFlag hE c ⟨0,hE⟩=true)
    (hmark : ∀n m,cyclicFlag hE c n=true→base n=base m→n=m)
    (hcollision : ∀n m,base n=base m→n=m ∨ c n≠c m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (cyclicFlag hE c))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (cyclicFlag hE c))→Bool)
    (hq : 0<Profile.cardinality (cyclicFlag hE c))
    (a b : Fin E) (ha : cyclicFlag hE c a=false) (hb : cyclicFlag hE c b=false)
    (hua : ∀n,base n=base a→n=a) (hub : ∀n,base n=base b→n=b)
    (hc : c a≠c b) (x : X) :
    ∃color,
      (∃n,foldVertex (cyclicFlag hE c) base C layers selectors color
        (AACFoldClock.numeric (cyclicFlag hE c) hq n)=(base a,x)) ∧
      (∃n,foldVertex (cyclicFlag hE c) base C layers selectors (!color)
        (AACFoldClock.numeric (cyclicFlag hE c) hq n)=(base b,x)) ∧
      (∀n,foldVertex (cyclicFlag hE c) base C layers selectors (!color)
        (AACFoldClock.numeric (cyclicFlag hE c) hq n)≠(base a,x)) ∧
      (∀n,foldVertex (cyclicFlag hE c) base C layers selectors color
        (AACFoldClock.numeric (cyclicFlag hE c) hq n)≠(base b,x)) := by
  let S := cyclicFlag hE c
  obtain ⟨o,ho⟩ := interior_complete hE S hcut a ha
  obtain ⟨p,hp⟩ := interior_complete hE S hcut b hb
  have hpar : o.1.val%2≠p.1.val%2 := ordinal_parity hE c hcut o p (by rw [ho,hp]; exact hc)
  have huo : ∀n,base n=base (interiorIndex S o)→n=interiorIndex S o := by rw [ho]; exact hua
  have hup : ∀n,base n=base (interiorIndex S p)→n=interiorIndex S p := by rw [hp]; exact hub
  let color := flipN o.1.val (!χ x)
  have hself (n : Nat) (v : Bool) : flipN n (flipN n v)=v := by
    induction n generalizing v with
    | zero => rfl
    | succ n ih => change flipN n (!(flipN n (!v)))=v; rw [←flipN_not,Bool.not_not,ih]
  have hs : χ x= !flipN o.1.val color := by simp only [color,hself,Bool.not_not]
  have hf : flipN p.1.val (!color)=flipN o.1.val color := by
    rw [flipN_mod,flipN_mod]
    have h0 := Nat.mod_lt o.1.val (by decide : 0<2)
    have h1 := Nat.mod_lt p.1.val (by decide : 0<2)
    by_cases hz : o.1.val%2=0
    · have hn : p.1.val%2≠0 := by omega
      simp only [hz,hn,↓reduceIte,Bool.not_not]
    · have hz' : p.1.val%2=0 := by omega
      simp only [hz,hz',↓reduceIte]
  have ht : χ x= !flipN p.1.val (!color) := by rw [hf]; exact hs
  have hma := (numeric_interior_mem_iff hE base c hcut hmark hcollision C layers selectors hq o huo x color).mpr hs
  have hmb := (numeric_interior_mem_iff hE base c hcut hmark hcollision C layers selectors hq p hup x (!color)).mpr ht
  rw [ho] at hma
  rw [hp] at hmb
  refine ⟨color,hma,hmb,?_,?_⟩
  · intro n hn
    have hh := (numeric_interior_mem_iff hE base c hcut hmark hcollision C layers selectors hq o huo x (!color)).mp
      ⟨n,by rw [ho]; exact hn⟩
    rw [flipN_not] at hh
    have he := hs.symm.trans hh
    cases hv : flipN o.1.val color <;> simp [hv] at he
  · intro n hn
    have hh := (numeric_interior_mem_iff hE base c hcut hmark hcollision C layers selectors hq p hup x color).mp
      ⟨n,by rw [hp]; exact hn⟩
    have ht' := ht
    rw [flipN_not] at ht'
    have he := ht'.symm.trans hh
    cases hv : flipN p.1.val color <;> simp [hv] at he

/-- The actual chronological isolated-turn geometry yields a normalized
fork. No folded membership/exclusion, interval parity, fork or output cycle
is supplied. The two incident edges belong to the original labelled host. -/
theorem isolated_fork {E : Nat} (hE : 0<E) (h2 : 2≤r)
    (base : Fin E→Y) (c : Fin E→Bool)
    (hcut : cyclicFlag hE c ⟨0,hE⟩=true)
    (hmark : ∀n m,cyclicFlag hE c n=true→base n=base m→n=m)
    (hcollision : ∀n m,base n=base m→n=m ∨ c n≠c m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (cyclicFlag hE c))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (cyclicFlag hE c))→Bool)
    (hq : 0<Profile.cardinality (cyclicFlag hE c))
    (hreturn : ∀v t,applyWord (word layers selectors v) (C.vertex (t,v))=C.vertex (successor hr t,v))
    (hedges : ∀n m,SameEdge (base n,base (successor hE n)) (base m,base (successor hE m))→n=m)
    (hlarge : 3≤(AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length)
    (a b : Fin E) (ha : cyclicFlag hE c a=false) (hb : cyclicFlag hE c b=false)
    (hua : ∀n,base n=base a→n=a) (hub : ∀n,base n=base b→n=b)
    (hc : c a≠c b) (u : Y) (x : X)
    (hea : AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers (u,x) (base a,x))
    (heb : AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers (u,x) (base b,x)) :
    ∃P : ForkTransfer.ForkPair (Y×X)
      (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length,
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers v w := by
  let S := cyclicFlag hE c
  let F := fun v n=>foldVertex S base C layers selectors v (AACFoldClock.numeric S hq n)
  have hinj (v : Bool) : Function.Injective (F v) :=
    AACFoldClock.physical_injective hE hr base c C layers selectors v hq hcut hmark hcollision
  have hp := AACFoldEdgeLedger.numeric_partition hE h2 S hcut base C layers selectors hq hreturn
    (fun j k he=>by
      have hm := hmark _ _ (markIndex_spec S j).1 he
      have hj := (markIndex_spec S j).2
      have hk := (markIndex_spec S k).2
      rw [hm] at hj
      exact Fin.ext (by omega)) hedges
  have huniq : ∀v n w m,SameEdge (F v n,F v (successor (AACFoldClock.length_pos hr S hq) n))
      (F w m,F w (successor (AACFoldClock.length_pos hr S hq) m))→v=w ∧ n=m := by
    intro v n w m he
    have hh := hp.2.1 (v,n) (w,m) he
    exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩
  obtain ⟨v,hma,hmb,hna,hnb⟩ := opposite_owners hE base c hcut hmark hcollision C layers selectors hq
    a b ha hb hua hub hc x
  obtain ⟨⟨va,i⟩,hi⟩ := hp.1 _ _ hea
  obtain ⟨⟨vb,j⟩,hj⟩ := hp.1 _ _ heb
  have hva : va=v := edge_owner_from_exclusion (AACFoldClock.length_pos hr S hq) F v va (base a,x) (u,x) i hi hna
  have hvb : vb= !v := edge_owner_from_exclusion (AACFoldClock.length_pos hr S hq) F (!v) vb (base b,x) (u,x) j hj
    (by simpa only [Bool.not_not] using hnb)
  subst va
  subst vb
  obtain ⟨P,s,eps,t,eta,hC,hD⟩ := normalize_pair (r:=r) hlarge F hinj huniq v (u,x) (base a,x) (base b,x) i j hi hj hna hnb
  refine ⟨P,?_⟩
  intro w z
  rw [normalized_union (r:=r) hlarge F v P s eps t eta hC hD]
  constructor
  · rintro ⟨cc,n,he⟩
    obtain ⟨label,hl⟩ := hp.2.2 (cc,n)
    exact ⟨label,sameEdge_trans hl he⟩
  · intro hh
    obtain ⟨⟨cc,n⟩,he⟩ := hp.1 w z hh
    exact ⟨cc,n,he⟩

/-- The actual fork transfer opens the isolated-turn cycle pair into two
simple paths with the unchanged exact host and unchanged common length. -/
noncomputable def isolated_paths {E : Nat} (hE : 0<E) (h2 : 2≤r)
    (base : Fin E→Y) (c : Fin E→Bool)
    (hcut : cyclicFlag hE c ⟨0,hE⟩=true)
    (hmark : ∀n m,cyclicFlag hE c n=true→base n=base m→n=m)
    (hcollision : ∀n m,base n=base m→n=m ∨ c n≠c m)
    (C : CycleData X R χ r hr)
    (layers : Fin (Profile.cardinality (cyclicFlag hE c))→CycleData X R χ r hr)
    (selectors : Fin (Profile.cardinality (cyclicFlag hE c))→Bool)
    (hq : 0<Profile.cardinality (cyclicFlag hE c))
    (hreturn : ∀v t,applyWord (word layers selectors v) (C.vertex (t,v))=C.vertex (successor hr t,v))
    (hedges : ∀n m,SameEdge (base n,base (successor hE n)) (base m,base (successor hE m))→n=m)
    (hlarge : 3≤(AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length)
    (a b : Fin E) (ha : cyclicFlag hE c a=false) (hb : cyclicFlag hE c b=false)
    (hua : ∀n,base n=base a→n=a) (hub : ∀n,base n=base b→n=b)
    (hc : c a≠c b) (u : Y) (x : X)
    (hea : AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers (u,x) (base a,x))
    (heb : AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers (u,x) (base b,x)) :
    GraphPathDecomposition (Y×X) (AACFoldEdgeLedger.HostAdjacent hE (cyclicFlag hE c) base layers)
      (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=r) hq)).length := by
  let P := Classical.choose (isolated_fork hE h2 base c hcut hmark hcollision C layers selectors hq hreturn
    hedges hlarge a b ha hb hua hub hc u x hea heb)
  have hP := Classical.choose_spec (isolated_fork hE h2 base c hcut hmark hcollision C layers selectors hq hreturn
    hedges hlarge a b ha hb hua hub hc u x hea heb)
  let D := P.decomposition
  exact {
    Index := D.Index
    indices := D.indices
    vertices := D.vertices
    simple := D.simple
    adjacent := fun p hp j=>(hP _ _).mp (D.adjacent p hp j)
    cover := fun v w hh=>D.cover v w ((hP v w).mpr hh)
    unique := D.unique
  }

/-- Literal occurrence transport through the actual cut rotation. This
retains the old vertex/color, unmarked status and physical uniqueness; it
never identifies cut positions with original chronological positions. -/
theorem rotate_occurrence {E : Nat} (hE : 0<E) (base : Fin E→Y) (c : Fin E→Bool)
    (cut old : Fin E) (hf : cyclicFlag hE c old=false)
    (hu : ∀p,base p=base old→p=old) :
    let a := backward hE old cut
    (fun p=>base (forward hE cut p)) a=base old ∧
    (fun p=>c (forward hE cut p)) a=c old ∧
    cyclicFlag hE (fun p=>c (forward hE cut p)) a=false ∧
    ∀p,(fun p=>base (forward hE cut p)) p=(fun p=>base (forward hE cut p)) a→p=a := by
  dsimp only
  have hi := forward_inverse hE cut old
  refine ⟨congrArg base hi,congrArg c hi,?_,?_⟩
  · rw [AACFirstMarkCut.cyclicFlag_rotate]
    change cyclicFlag hE c (forward hE cut (backward hE old cut))=false
    rw [hi]
    exact hf
  · intro p hp
    apply forward_injective hE cut
    rw [hi]
    apply hu
    rw [hi] at hp
    exact hp

/-- Actual ordinary-source specialization. The only additional inputs are
literal chronological neighbor geometry, discharged by isolated turns.
Schedule return, edge ledger, size and folded ownership are internal. -/
theorem source_pair (hj : 0<r) (I : SourceLocalFold.Input) (h2 : 2≤r)
    (cycles : Fin (I.m*I.b)→CycleData X R χ r hj) (n : I.Index)
    (a b : Fin I.E) (ha : I.flag n a=false) (hb : I.flag n b=false)
    (hua : ∀p,I.base n p=I.base n a→p=a) (hub : ∀p,I.base n p=I.base n b→p=b)
    (hc : I.color n a≠I.color n b) (u : I.Y)
    (hea : I.Host n u (I.base n a)) (heb : I.Host n u (I.base n b)) :
    ∃P : ForkTransfer.ForkPair (I.Y×X) (I.length (jR:=r) n),
      ∀v w,P.unionRelation v w ↔ AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
        (I.layers hj cycles n) v w := by
  have hword := SourceGlobalMarks.word_length I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd n
  change 4≤(I.marks.word n).length at hword
  have hlength := (I.decomposition hj h2 cycles n).2.2.2.2
  have hlarge : 3≤I.length (jR:=r) n := by
    rw [hlength]
    have hm := Nat.mul_le_mul h2 (show 4≤I.E+(I.marks.word n).length by omega)
    omega
  have hreturn := AACFoldEdgeLedger.forest_return (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)
  let x := (cycles (I.schedule.active n)).vertex (⟨0,hj⟩,false)
  have hea' : AACFoldEdgeLedger.HostAdjacent I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (u,x) (I.base n a,x) :=
    (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (I.Host n) (I.host_cover n) _ _).mpr (Or.inl ⟨rfl,hea⟩)
  have heb' : AACFoldEdgeLedger.HostAdjacent I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (u,x) (I.base n b,x) :=
    (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n) (I.layers hj cycles n)
      (I.Host n) (I.host_cover n) _ _).mpr (Or.inl ⟨rfl,heb⟩)
  obtain ⟨P,hP⟩ := isolated_fork I.epos h2 (I.base n) (I.color n) (I.cut_mark n)
    (I.mark_unique n) (I.collision n) (cycles (I.schedule.active n)) (I.layers hj cycles n)
    (I.selectors hj cycles n) (I.qpos n) hreturn (I.edge_unique n) hlarge
    a b ha hb hua hub hc u x hea' heb'
  refine ⟨P,?_⟩
  intro v w
  exact (hP v w).trans (AACFoldEdgeLedger.host_iff I.epos (I.flag n) (I.base n)
    (I.layers hj cycles n) (I.Host n) (I.host_cover n) v w)

/-- Exact local path decomposition from the actual source isolated geometry. -/
noncomputable def source_paths (hj : 0<r) (I : SourceLocalFold.Input) (h2 : 2≤r)
    (cycles : Fin (I.m*I.b)→CycleData X R χ r hj) (n : I.Index)
    (a b : Fin I.E) (ha : I.flag n a=false) (hb : I.flag n b=false)
    (hua : ∀p,I.base n p=I.base n a→p=a) (hub : ∀p,I.base n p=I.base n b→p=b)
    (hc : I.color n a≠I.color n b) (u : I.Y)
    (hea : I.Host n u (I.base n a)) (heb : I.Host n u (I.base n b)) :
    GraphPathDecomposition (I.Y×X)
      (AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n) (I.layers hj cycles n))
      (I.length (jR:=r) n) := by
  let P := Classical.choose (source_pair hj I h2 cycles n a b ha hb hua hub hc u hea heb)
  have hP := Classical.choose_spec (source_pair hj I h2 cycles n a b ha hb hua hub hc u hea heb)
  let D := P.decomposition
  exact {
    Index := D.Index
    indices := D.indices
    vertices := D.vertices
    simple := D.simple
    adjacent := fun p hp j=>(hP _ _).mp (D.adjacent p hp j)
    cover := fun v w hh=>D.cover v w ((hP v w).mpr hh)
    unique := D.unique
  }

#print axioms source_paths
#print axioms source_pair
#print axioms rotate_occurrence
#print axioms ordinal_parity
#print axioms opposite_owners
#print axioms isolated_fork
#print axioms isolated_paths
end ErdePaths.AACIsolatedOpening
