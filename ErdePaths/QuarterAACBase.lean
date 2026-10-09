import ErdePaths.QuarterGlobalMarks
import ErdePaths.QuarterFactorGeometry
import ErdePaths.QuarterPatternGeometry
import ErdePaths.SourceGlobalMarks
import ErdePaths.AACFirstMarkCut
import ErdePaths.AACFoldEdgeLedger
import ErdePaths.UniformFoldLengths

namespace ErdePaths.QuarterAACBase
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
open AACMarkIntervals AACIntervalSplit AACFirstMarkCut SubdividedWiggle
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

/-- Genuine quarter inputs. Profiles, paired origins and zero upper depth
are fixed internally; no word, mark count, fork or output tour is supplied. -/
structure Input where
  e : Nat
  d : Nat
  m : Nat
  B : Nat
  hB : 0<B
  he : 2≤e
  D : DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e)
  HD : DecompositionData (Vertex d) (@Adjacent d) (m*2) B hB
  last : Vertex d
  hB4 : 4≤B
  evenB : B%2=0

namespace Input
abbrev Y (I : Input) := SourceGlobalMarks.Physical I.e I.d 1 0
abbrev K (I : Input) := QuarterPhysicalIncidence.K I.e
def E (I : Input) := I.K*I.B*(2+1)
theorem epos (I : Input) : 0<I.E := Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) I.hB) (by decide)
abbrev Index (I : Input) := Fin (I.m*4)
def factor (I : Input) (n : I.Index) := SourceGlobalMarks.sourceIndex 1 0 1 n
noncomputable def assigned (I : Input) (f : Fin I.m) (eps : Bool) (a : Address 1) : Fin (I.m*2) :=
  OriginFactors.association 1 0 (by decide) (SourceFactors.index 1 0 f eps a)
noncomputable def marks (I : Input) :=
  QuarterGlobalMarks.marks I.D I.he I.hB I.hB4 I.evenB I.HD I.last I.assigned
noncomputable def schedule (I : Input) : MarkSchedule.Data I.marks :=
  QuarterGlobalMarks.schedule I.D I.he I.hB I.hB4 I.evenB I.HD I.last I.assigned
noncomputable def G (I : Input) (n : I.Index) : ClockData (VertexPower (Vertex I.e) 1×VertexPower (Vertex I.e) 1) (I.K*2) :=
  ((OriginFactors.Quarter.factors I.D I.he (⟨1,by decide⟩ : Fin 2)).cycles (I.factor n)).toClockData
noncomputable def H (I : Input) (n : I.Index) : ClockData (Vertex I.d) I.B :=
  ((HamiltonCommonLast.normalize I.HD I.last).cycles (OriginFactors.association 1 0 (by decide) (I.factor n))).toClockData
noncomputable def euler (I : Input) := QuarterPatternGeometry.euler (Nat.two_pow_pos _) I.hB (QuarterPhysicalIncidence.period I.he)
noncomputable def originalBase (I : Input) (n : I.Index) : Fin I.E→I.Y :=
  QuarterFactorGeometry.sourceBase I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
    (⟨1,by decide⟩ : Fin 2) (I.factor n)
noncomputable def originalColor (I : Input) : Fin I.E→Bool :=
  AACMarkIntervals.numericColor (Nat.two_pow_pos _) (by decide : 0<2) I.hB I.euler.orbit I.euler.length (⟨1,by decide⟩ : Fin 2)
noncomputable def originalFlag (I : Input) := cyclicFlag I.epos I.originalColor
noncomputable def originalWord (I : Input) (n : I.Index) := (indices I.originalFlag).map (I.originalBase n)

theorem word_lookup (I : Input) (n : I.Index) : I.originalWord n=I.marks.word n := by
  let p := AnchoredEmbedding.positionDecode (by decide : 0<4) n
  have hn := AnchoredEmbedding.positionEncode_decode (by decide : 0<4) n
  change AnchoredEmbedding.positionEncode p.1 p.2=n at hn
  rw [←hn]
  unfold marks
  rw [QuarterGlobalMarks.word_lookup]
  unfold originalWord originalFlag originalColor originalBase factor
  rw [SourceGlobalMarks.sourceIndex_lookup]
  unfold QuarterFactorGeometry.sourceBase SourceAACBase.base QuarterChronologicalMarks.word AACMarkIntervals.markWord
  simp only [List.map_map,Function.comp_def]
  rw [QuarterFactorGeometry.clock_eq]
  rfl

theorem flag_card (I : Input) (n : I.Index) : Profile.cardinality I.originalFlag=(I.marks.word n).length := by
  rw [←word_lookup,originalWord,List.length_map,indices_length]

theorem word_length (I : Input) (n : I.Index) : 4≤(I.marks.word n).length :=
  QuarterGlobalMarks.global_word_length I.D I.he I.hB I.hB4 I.evenB I.HD I.last I.assigned n

theorem flag_pos (I : Input) (n : I.Index) : 0<Profile.cardinality I.originalFlag := by
  have hh := I.word_length n
  rw [←I.flag_card n] at hh
  omega

noncomputable def Host (I : Input) (n : I.Index) :=
  QuarterFactorGeometry.Host I.D I.he (HamiltonCommonLast.normalize I.HD I.last) (⟨1,by decide⟩ : Fin 2) (I.factor n)

theorem sizes (I : Input) : 3≤I.K*2 ∧ 2≤I.E := by
  have hk : 4≤I.K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period I.he)
  have hb := I.hB4
  constructor
  · omega
  · have hm := Nat.mul_le_mul hk hb
    change 2≤I.K*I.B*(2+1)
    omega

theorem original_mark_unique (I : Input) (n : I.Index) (p q : Fin I.E)
    (hp : I.originalFlag p=true) (hh : I.originalBase n p=I.originalBase n q) : p=q :=
  SourceAACBase.mark_unique (Nat.two_pow_pos _) (by decide : 0<2) I.hB I.euler (I.G n) (I.H n)
    I.sizes.1 (by have := I.hB4; omega) I.evenB I.sizes.2 (⟨1,by decide⟩ : Fin 2) (by decide) p q hp hh

theorem original_collision (I : Input) (n : I.Index) (p q : Fin I.E)
    (hh : I.originalBase n p=I.originalBase n q) : p=q ∨ I.originalColor p≠I.originalColor q :=
  SourceAACBase.color_collision (Nat.two_pow_pos _) (by decide : 0<2) I.hB I.euler (I.G n) (I.H n)
    I.sizes.1 (by have := I.hB4; omega) I.evenB I.sizes.2 (⟨1,by decide⟩ : Fin 2) (by decide) p q hh

theorem original_host_cover (I : Input) (n : I.Index) (x y : I.Y) : I.Host n x y ↔
    ∃p,SameEdge (I.originalBase n p,I.originalBase n (successor I.epos p)) (x,y) :=
  QuarterFactorGeometry.source_host_iff I.D I.he (HamiltonCommonLast.normalize I.HD I.last)
    (⟨1,by decide⟩ : Fin 2) (I.factor n) x y

theorem original_edge_unique (I : Input) (n : I.Index) (p q : Fin I.E)
    (hh : SameEdge (I.originalBase n p,I.originalBase n (successor I.epos p))
      (I.originalBase n q,I.originalBase n (successor I.epos q))) : p=q :=
  SourceAACBase.edge_unique (Nat.two_pow_pos _) (by decide : 0<2) I.hB I.euler (I.G n) (I.H n)
    I.sizes.1 (by have := I.hB4; omega) p q hh

noncomputable def first (I : Input) (n : I.Index) : Fin I.E := cut I.originalFlag (I.flag_pos n)
noncomputable def base (I : Input) (n : I.Index) (p : Fin I.E) : I.Y :=
  I.originalBase n (forward I.epos (I.first n) p)
noncomputable def color (I : Input) (n : I.Index) (p : Fin I.E) : Bool :=
  I.originalColor (forward I.epos (I.first n) p)
noncomputable def flag (I : Input) (n : I.Index) : Fin I.E→Bool := cyclicFlag I.epos (I.color n)

theorem flag_eq (I : Input) (n : I.Index) : I.flag n=flags I.epos I.originalFlag (I.first n) :=
  cyclicFlag_rotate I.epos I.originalColor (I.first n)

theorem cut_mark (I : Input) (n : I.Index) : I.flag n ⟨0,I.epos⟩=true := by
  rw [flag_eq]
  exact cut_zero I.epos I.originalFlag (I.flag_pos n)

theorem mark_card (I : Input) (n : I.Index) : Profile.cardinality (I.flag n)=(I.marks.word n).length := by
  rw [flag_eq,first,cardinality_rotate]
  exact I.flag_card n

theorem word_cut (I : Input) (n : I.Index) : (indices (I.flag n)).map (I.base n)=I.marks.word n := by
  rw [flag_eq]
  have hh := word_rotate I.epos I.originalFlag (I.flag_pos n) (I.originalBase n)
  exact hh.trans (I.word_lookup n)

/-- Exact scheduled ordinal lookup at the actual rotated physical mark. -/
theorem marked_lookup (I : Input) (n : I.Index) (j : Fin (Profile.cardinality (I.flag n))) :
    I.base n (markIndex (I.flag n) j)=(I.marks.word n)[j.val]'(by rw [←I.mark_card n]; exact j.isLt) := by
  have hw := I.word_cut n
  rw [indices_markIndex,List.map_map] at hw
  have hv := congrArg (fun ls : List I.Y=>ls[j.val]?) hw
  simp only [List.finRange,List.map_ofFn,List.getElem?_ofFn,j.isLt,↓reduceDIte,
    Function.comp_def,List.getElem?_eq_getElem (show j.val<(I.marks.word n).length by rw [←I.mark_card n]; exact j.isLt)] at hv
  exact Option.some.inj hv

theorem mark_unique (I : Input) (n : I.Index) (p q : Fin I.E)
    (hp : I.flag n p=true) (he : I.base n p=I.base n q) : p=q := by
  apply forward_injective I.epos (I.first n)
  apply I.original_mark_unique n
  · rw [I.flag_eq n] at hp
    exact hp
  · exact he

theorem collision (I : Input) (n : I.Index) (p q : Fin I.E) (he : I.base n p=I.base n q) :
    p=q ∨ I.color n p≠I.color n q := by
  have hh := I.original_collision n _ _ he
  exact hh.elim (fun he=>Or.inl (forward_injective I.epos (I.first n) he)) Or.inr

theorem host_cover (I : Input) (n : I.Index) (x y : I.Y) : I.Host n x y ↔
    ∃p, SameEdge (I.base n p,I.base n (successor I.epos p)) (x,y) := by
  rw [I.original_host_cover n]
  constructor
  · rintro ⟨q,hq⟩
    let p := backward I.epos q (I.first n)
    have hp : forward I.epos (I.first n) p=q := forward_inverse I.epos _ _
    refine ⟨p,?_⟩
    change SameEdge (I.originalBase n (forward I.epos (I.first n) p),
      I.originalBase n (forward I.epos (I.first n) (successor I.epos p))) (x,y)
    rw [HamiltonNormalize.forward_successor,hp]
    exact hq
  · rintro ⟨p,hp⟩
    refine ⟨forward I.epos (I.first n) p,?_⟩
    change SameEdge (I.originalBase n (forward I.epos (I.first n) p),
      I.originalBase n (successor I.epos (forward I.epos (I.first n) p))) (x,y)
    rw [←HamiltonNormalize.forward_successor]
    exact hp

theorem edge_unique (I : Input) (n : I.Index) (p q : Fin I.E)
    (he : SameEdge (I.base n p,I.base n (successor I.epos p))
      (I.base n q,I.base n (successor I.epos q))) : p=q := by
  apply forward_injective I.epos (I.first n)
  apply I.original_edge_unique n
  change SameEdge (I.originalBase n (forward I.epos (I.first n) p),
    I.originalBase n (successor I.epos (forward I.epos (I.first n) p)))
    (I.originalBase n (forward I.epos (I.first n) q),
    I.originalBase n (successor I.epos (forward I.epos (I.first n) q)))
  simpa only [base,HamiltonNormalize.forward_successor] using he

theorem qpos (I : Input) (n : I.Index) : 0<Profile.cardinality (I.flag n) :=
  AACFoldClock.cardinality_pos I.epos (I.flag n) (I.cut_mark n)

section Fold
variable {X : Type} {R : X→X→Prop} {χ : X→Bool} {jR : Nat} (hj : 0<jR)

/-- Actual schedule descriptors have exactly the actual geometric mark count. -/
theorem descriptor_card (I : Input) (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Profile.cardinality (I.flag n)=
      (LayerPartition.descriptors (cycles (I.schedule.active n)) cycles
        (I.schedule.inside n) (I.schedule.outside n)).length := by
  have hh := congrArg List.length (MarkSchedule.descriptor_order I.schedule cycles n)
  simp only [List.length_map,List.length_finRange] at hh
  exact (I.mark_card n).trans hh.symm

noncomputable def layers (I : Input) (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→PairedLayers.CycleData X R χ jR hj :=
  AACFoldEdgeLedger.forestLayers (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

noncomputable def selectors (I : Input) (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→Bool :=
  AACFoldEdgeLedger.forestSelectors (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

/-- The literal J cycle at every actual marked ordinal is precisely the
global palette label at the unchanged chronological word occurrence. -/
theorem layer_lookup (I : Input) (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) (j : Fin (Profile.cardinality (I.flag n))) :
    I.layers hj cycles n j=cycles (I.schedule.labels n (Fin.cast (I.mark_card n) j)) := by
  have hh := MarkSchedule.descriptor_order I.schedule cycles n
  have hd : j.val<(LayerPartition.descriptors (cycles (I.schedule.active n)) cycles
        (I.schedule.inside n) (I.schedule.outside n)).length := by
    rw [←I.descriptor_card hj cycles n]; exact j.isLt
  have hw : j.val<(I.marks.word n).length := by rw [←I.mark_card n]; exact j.isLt
  have hv := congrArg (fun ls : List (PairedLayers.CycleData X R χ jR hj)=>ls[j.val]?) hh
  simp only [List.getElem?_map,List.getElem?_eq_getElem hd,Option.map_some,
    List.finRange,List.map_ofFn,List.getElem?_ofFn,hw,↓reduceDIte,Function.comp_def] at hv
  exact Option.some.inj hv

noncomputable def length (I : Input) (n : I.Index) : Nat :=
  (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=jR) (I.qpos n))).length

theorem length_pos (I : Input) (hJ : 0<jR) (n : I.Index) : 0<I.length (jR:=jR) n :=
  AACFoldClock.length_pos hJ (I.flag n) (I.qpos n)

noncomputable def tour (I : Input) (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) (color : Bool) : Fin (I.length (jR:=jR) n)→I.Y×X :=
  AACFoldClock.physical I.epos hj (I.base n) (I.color n) (cycles (I.schedule.active n))
    (I.layers hj cycles n) (I.selectors hj cycles n) color (I.qpos n)

/-- Actual two simple numeric tours and complete literal local input-host
partition. Geometry, descriptor size, return, schedule and coverage are all
derived from the actual source and the internally constructed global schedule. -/
theorem decomposition (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*1)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
    (∀color, Function.Injective (I.tour hj cycles n color)) ∧
    (∀x y, AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n)
      (I.layers hj cycles n) x y→∃color p, SameEdge
        (I.tour hj cycles n color p,I.tour hj cycles n color (successor (I.length_pos hj n) p)) (x,y)) ∧
    (∀color p color' p', SameEdge
      (I.tour hj cycles n color p,I.tour hj cycles n color (successor (I.length_pos hj n) p))
      (I.tour hj cycles n color' p',I.tour hj cycles n color' (successor (I.length_pos hj n) p'))→
        color=color' ∧ p=p') ∧
    (∀color p, AACFoldEdgeLedger.InputHost (I.Host n) (I.flag n) (I.base n) (I.layers hj cycles n)
      (I.tour hj cycles n color p) (I.tour hj cycles n color (successor (I.length_pos hj n) p))) ∧
    I.length (jR:=jR) n=jR*(I.E+(I.marks.word n).length) := by
  have hp := AACFoldEdgeLedger.aac_decomposition I.epos h2 (I.base n) (I.color n)
    (I.cut_mark n) (I.mark_unique n) (I.collision n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)
    (I.edge_unique n) (I.Host n) (I.host_cover n)
  refine ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,?_⟩
  change (AACFoldClock.Weighted.all (AACFoldClock.scalarWeight (r:=jR) (I.qpos n))).length=_
  rw [AACFoldClock.length_eq I.epos (I.flag n) (I.cut_mark n) (I.qpos n),I.mark_card n]

end Fold

theorem word_length_exact (I : Input) (n : I.Index) :
    (I.marks.word n).length=(I.K/2)*I.B := by
  rw [←I.flag_card n]
  have hk : 4≤I.K := Nat.le_of_dvd (Nat.two_pow_pos _) (QuarterPhysicalIncidence.period I.he)
  have hh := AACPatternCardinality.anti_cardinality (by omega : 1<I.K) (by decide : 0<2) I.hB
    I.sizes.1 (by have := I.hB4; omega) I.evenB (by decide : 0<2)
    (QuarterPhysicalIncidence.period I.he) (by decide : 1<2) (by decide : 2%2=0) (by decide : 1%2=1)
    (I.B-1) I.euler.orbit I.euler.length I.epos I.sizes.2 I.euler.injective I.euler.surjective
    (⟨1,by decide⟩ : Fin 2) (by decide)
  change Profile.cardinality I.originalFlag=1*(I.K/2)*I.B at hh
  simpa only [Nat.one_mul] using hh

end Input
#print axioms Input.original_mark_unique
#print axioms Input.original_collision
#print axioms Input.original_host_cover
#print axioms Input.original_edge_unique
end ErdePaths.QuarterAACBase
