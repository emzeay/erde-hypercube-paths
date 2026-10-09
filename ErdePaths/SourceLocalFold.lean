import ErdePaths.SourceAACBase
import ErdePaths.SourceGlobalMarks
import ErdePaths.AACFirstMarkCut
import ErdePaths.AACFoldEdgeLedger

namespace ErdePaths.SourceLocalFold
open SourceClock SourceProfile HamiltonData HamiltonTower HierarchicalDecode SquareLift
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq
open AACMarkIntervals AACIntervalSplit AACFirstMarkCut SubdividedWiggle

/-- Genuine source/cube inputs. No base word, geometric ownership, schedule,
return law or output tour appears among these fields. -/
structure Input where
  e : Nat
  d : Nat
  m : Nat
  u : Nat
  B : Nat
  b : Nat
  a : Nat
  h : Nat
  r : Nat
  hB : 0<B
  he : 2≤e
  hr : r<a+h+1
  hh : 0<h
  room : 2^(a+h+1)∣lengthPower (2^e) a
  hA : 2*u=2^r
  D : DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e)
  S : Fin m→Address a→Fin (2^(e*2^a))→Bool
  ho : ∀f address, Profile.cardinality (S f address)%2=1
  balance : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u
  HD : DecompositionData (Vertex d) (@Adjacent d) (m*(2*2^(a+h-r))) B hB
  last : Vertex d
  z : Fin (2^r)
  hz : 0<z.val
  hB4 : 4≤B
  evenB : B%2=0
  short : b<2^(a+h+1-r)
  odd : b%2=1

namespace Input
abbrev Y (I : Input) := SourceGlobalMarks.Physical I.e I.d I.a I.h
def E (I : Input) : Nat := 2^(I.e*2^(I.a+I.h+1)-I.r)*I.B*(2^I.r+1)
theorem epos (I : Input) : 0<I.E := Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) I.hB) (by have := Nat.two_pow_pos I.r; omega)
abbrev Index (I : Input) := Fin (I.m*2^(I.a+I.h+1))

noncomputable def assigned (I : Input) (f : Fin I.m) (eps : Bool) (address : Address (I.a+I.h)) :
    Fin (I.m*(2*2^(I.a+I.h-I.r))) :=
  SourceHostPartition.association I.a I.h I.r I.hr (SourceFactors.index I.a I.h f eps address)

noncomputable def marks (I : Input) :=
  SourceGlobalMarks.marks I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance
    I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd
noncomputable def schedule (I : Input) : MarkSchedule.Data I.marks :=
  SourceGlobalMarks.schedule I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance
    I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd

def factor (I : Input) (n : I.Index) := SourceGlobalMarks.sourceIndex I.a I.h I.r n
noncomputable def originalBase (I : Input) (n : I.Index) : Fin I.E→I.Y :=
  SourceAACBase.sourceBase (b:=I.b) I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.HD I.last I.z (I.factor n)
noncomputable def originalColor (I : Input) : Fin I.E→Bool :=
  SourceAACBase.sourceColor (b:=I.b) (hB:=I.hB) I.he I.a I.h I.r I.hr I.z
noncomputable def originalFlag (I : Input) := cyclicFlag I.epos I.originalColor
noncomputable def originalWord (I : Input) (n : I.Index) : List I.Y :=
  SourceAACBase.sourceWord (b:=I.b) I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.HD I.last I.z (I.factor n)

/-- The actual original source word is the literal ordered global word. -/
theorem word_lookup (I : Input) (n : I.Index) : I.originalWord n=I.marks.word n := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (I.a+I.h+1)) n
  have hn := AnchoredEmbedding.positionEncode_decode (Nat.two_pow_pos (I.a+I.h+1)) n
  change AnchoredEmbedding.positionEncode p.1 p.2=n at hn
  rw [←hn]
  unfold originalWord factor
  rw [SourceGlobalMarks.sourceIndex_lookup,SourceAACBase.source_word_lookup]
  exact (SourceGlobalMarks.word_lookup I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd p.1 p.2).symm

theorem word_indices (I : Input) (n : I.Index) :
    I.originalWord n=(indices I.originalFlag).map (I.originalBase n) := rfl

theorem flag_card (I : Input) (n : I.Index) : Profile.cardinality I.originalFlag=(I.marks.word n).length := by
  rw [←word_lookup,word_indices,List.length_map,indices_length]

theorem flag_pos (I : Input) (n : I.Index) : 0<Profile.cardinality I.originalFlag := by
  have hlen := SourceGlobalMarks.word_length I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.z I.hz I.hB I.hB4 I.evenB I.HD I.last I.assigned I.short I.odd n
  change 4≤(I.marks.word n).length at hlen
  rw [←flag_card I n] at hlen
  omega

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
  exact hh.trans ((I.word_indices n).symm.trans (I.word_lookup n))

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
  apply SourceAACBase.source_mark_unique (b:=I.b) I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.HD I.last (by have := I.hB4; omega) I.evenB I.z I.hz (I.factor n)
  · rw [I.flag_eq n] at hp
    exact hp
  · exact he

theorem collision (I : Input) (n : I.Index) (p q : Fin I.E) (he : I.base n p=I.base n q) :
    p=q ∨ I.color n p≠I.color n q := by
  have hh := SourceAACBase.source_collision (b:=I.b) I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.HD I.last (by have := I.hB4; omega) I.evenB I.z I.hz (I.factor n) _ _ he
  exact hh.elim (fun he=>Or.inl (forward_injective I.epos (I.first n) he)) Or.inr

noncomputable def Host (I : Input) (n : I.Index) :=
  SourceHostPartition.Host I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA I.S I.ho I.balance
    (HamiltonCommonLast.normalize I.HD I.last) I.z (I.factor n)

theorem host_cover (I : Input) (n : I.Index) (x y : I.Y) : I.Host n x y ↔
    ∃p, SameEdge (I.base n p,I.base n (successor I.epos p)) (x,y) := by
  unfold Host
  rw [SourceAACBase.source_host_iff (b:=I.b)]
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
  apply SourceAACBase.source_edge_unique (b:=I.b) I.D I.he I.a I.h I.r I.hr I.hh I.room I.hA
    I.S I.ho I.balance I.HD I.last (by have := I.hB4; omega) I.z (I.factor n)
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
theorem descriptor_card (I : Input) (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Profile.cardinality (I.flag n)=
      (LayerPartition.descriptors (cycles (I.schedule.active n)) cycles
        (I.schedule.inside n) (I.schedule.outside n)).length := by
  have hh := congrArg List.length (MarkSchedule.descriptor_order I.schedule cycles n)
  simp only [List.length_map,List.length_finRange] at hh
  exact (I.mark_card n).trans hh.symm

noncomputable def layers (I : Input) (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→PairedLayers.CycleData X R χ jR hj :=
  AACFoldEdgeLedger.forestLayers (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

noncomputable def selectors (I : Input) (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→Bool :=
  AACFoldEdgeLedger.forestSelectors (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

/-- The literal J cycle at every actual marked ordinal is precisely the
global palette label at the unchanged chronological word occurrence. -/
theorem layer_lookup (I : Input) (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj)
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

noncomputable def tour (I : Input) (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) (color : Bool) : Fin (I.length (jR:=jR) n)→I.Y×X :=
  AACFoldClock.physical I.epos hj (I.base n) (I.color n) (cycles (I.schedule.active n))
    (I.layers hj cycles n) (I.selectors hj cycles n) color (I.qpos n)

/-- Actual two simple numeric tours and complete literal local input-host
partition. Geometry, descriptor size, return, schedule and coverage are all
derived from the actual source and the internally constructed global schedule. -/
theorem decomposition (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*I.b)→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
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

end Input
#print axioms Input.word_lookup
#print axioms Input.marked_lookup
#print axioms Input.layer_lookup
#print axioms Input.decomposition
end ErdePaths.SourceLocalFold
