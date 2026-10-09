import ErdePaths.SourceAACBase
import ErdePaths.ZeroUpperGlobalMarks
import ErdePaths.ZeroUpperFactors
import ErdePaths.SourceLocalFold
import ErdePaths.UniformFoldLengths

namespace ErdePaths.ZeroUpperAACBase
open SourceClock SquareLift AACTransition AACFine AACFineClock AACMarkIntervals SubdividedWiggle
open SourceProfile HamiltonData HamiltonTower HierarchicalDecode AnchoredEmbedding
open SourceAACBase AACIntervalSplit AACFirstMarkCut
set_option warn.classDefReducibility false
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

section Source
variable {V W : Type} {R : V→V→Prop} {T : W→W→Prop} {m e B : Nat} {hB : 0<B}
  (D : DecompositionData V R m (2^e) (Nat.two_pow_pos e)) (he : 2≤e)
  (k : Nat) (hk : 2≤k)
  (room : 2^(k+0+3)∣lengthPower (2^e) k)
  (exceptional : Bool)
  (HD : DecompositionData W T (m*(2*2^(k+0-1))) B hB) (last : W)

/-- Actual G Hamilton clock of the owned factor. -/
noncomputable def G (z : Fin (2)) (i : Fin (count (2*count m k) 0)) :
    ClockData (VertexPower (VertexPower V k×VertexPower V k) 0) (2^(e*2^(k+0+1)-1)*2) :=
  ((ZeroUpperFactors.Actual.factors D he k hk room exceptional z).cycles i).toClockData

/-- Actual canonically assigned H clock, with its physical omission derived
by the genuine common-last normalization. -/
noncomputable def H (i : Fin (count (2*count m k) 0)) : ClockData W B :=
  ((HamiltonCommonLast.normalize HD last).cycles (ZeroUpperFactors.association k 0 hk i)).toClockData

/-- The exact literal geometric host is the already proved actual source
host, with actual normalized H factors and actual canonical association. -/
theorem gridHost_source (z : Fin (2)) (i : Fin (count (2*count m k) 0))
    (x y : VertexPower (VertexPower V k×VertexPower V k) 0×W) :
    GridHost (Nat.two_pow_pos (e*2^(k+0+1)-1)) (show 0<2 by decide) hB
      (G D he k hk room exceptional z i) (H k hk HD last i) x y ↔
    ZeroUpperFactors.Actual.Host D he k hk room exceptional
      (HamiltonCommonLast.normalize HD last) z i x y := by
  exact ZeroUpperFactors.Actual.grid_host_iff D he k hk room exceptional
    (HamiltonCommonLast.normalize HD last) z i x y

/-- Actual unrotated physical AAC Euler word, constructed uniformly. -/
noncomputable def sourceBase (z : Fin (2)) (i : Fin (count (2*count m k) 0))
    (n : Fin (2^(e*2^(k+0+1)-1)*B*(2+1))) :
    VertexPower (VertexPower V k×VertexPower V k) 0×W :=
  base (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB)
    (G D he k hk room exceptional z i) (H k hk HD last i) n

/-- Derived actual source-host iff its literal successive physical AAC base
edge ledger, with no supplied host coverage or traversal existence. -/
theorem source_host_iff (z : Fin (2)) (i : Fin (count (2*count m k) 0))
    (x y : VertexPower (VertexPower V k×VertexPower V k) 0×W) :
    ZeroUpperFactors.Actual.Host D he k hk room exceptional
      (HamiltonCommonLast.normalize HD last) z i x y ↔
    ∃n : Fin (2^(e*2^(k+0+1)-1)*B*(2+1)), SameEdge
      (sourceBase D he k hk room exceptional HD last z i n,
       sourceBase D he k hk room exceptional HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n)) (x,y) := by
  rw [←gridHost_source D he k hk room exceptional HD last z i]
  exact gridHost_iff (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB) _ _ x y

include he hk hB in
private theorem source_sizes :
    3≤2^(e*2^(k+0+1)-1)*2 ∧ 2≤2^(e*2^(k+0+1)-1)*B*(2+1) := by
  have hk4 := SourceLengths.coarse_size he k 0 1 (by omega)
  have haPos := show 0<2 by decide
  have hm := Nat.mul_le_mul_left (2^(e*2^(k+0+1)-1))
    (show 1≤2 from show 0<2 by decide)
  have hb1 : 1≤B := hB
  have hmB := Nat.mul_le_mul_left (2^(e*2^(k+0+1)-1)) hb1
  have hmE := Nat.mul_le_mul_left (2^(e*2^(k+0+1)-1)*B) (show 1≤2+1 by omega)
  simp only [Nat.mul_one] at hm hmB hmE
  omega

/-- Concrete source base edges are genuine edges of their exact owned host. -/
theorem source_adjacent (z : Fin (2)) (i : Fin (count (2*count m k) 0))
    (n : Fin (2^(e*2^(k+0+1)-1)*B*(2+1))) :
    ZeroUpperFactors.Actual.Host D he k hk room exceptional
      (HamiltonCommonLast.normalize HD last) z i
      (sourceBase D he k hk room exceptional HD last z i n)
      (sourceBase D he k hk room exceptional HD last z i
        (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n)) :=
  (source_host_iff D he k hk room exceptional HD last z i _ _).mpr ⟨n,Or.inl rfl⟩

/-- Actual source specialization: size bounds are derived, not supplied. -/
theorem source_edge_unique (hB3 : 3≤B) (z : Fin (2)) (i : Fin (count (2*count m k) 0))
    (n n' : Fin (2^(e*2^(k+0+1)-1)*B*(2+1)))
    (heq : SameEdge
      (sourceBase D he k hk room exceptional HD last z i n,
       sourceBase D he k hk room exceptional HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n))
      (sourceBase D he k hk room exceptional HD last z i n',
       sourceBase D he k hk room exceptional HD last z i
         (successor (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) n'))) : n=n' :=
  edge_unique (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB) _ _
    (source_sizes (hB:=hB) he k hk).1 hB3 n n' heq

/-- Literal interval color of the actual original source Euler word. -/
noncomputable def sourceColor (z : Fin (2)) (n : Fin (2^(e*2^(k+0+1)-1)*B*(2+1))) : Bool :=
  numericColor (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB).orbit
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB).length z n

theorem source_collision (hB3 : 3≤B) (hbeven : B%2=0) (z : Fin (2)) (hz : 0<z.val)
    (i : Fin (count (2*count m k) 0)) (n n' : Fin (2^(e*2^(k+0+1)-1)*B*(2+1)))
    (heq : sourceBase D he k hk room exceptional HD last z i n=
      sourceBase D he k hk room exceptional HD last z i n') :
    n=n' ∨ sourceColor (hB:=hB) he k hk z n≠sourceColor (hB:=hB) he k hk z n' :=
  color_collision (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB) _ _
    (source_sizes (hB:=hB) he k hk).1 hB3 hbeven (source_sizes (hB:=hB) he k hk).2 z hz n n' heq

theorem source_mark_unique (hB3 : 3≤B) (hbeven : B%2=0) (z : Fin (2)) (hz : 0<z.val)
    (i : Fin (count (2*count m k) 0)) (n n' : Fin (2^(e*2^(k+0+1)-1)*B*(2+1)))
    (hn : cyclicFlag (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega))
      (sourceColor (hB:=hB) he k hk z) n=true)
    (heq : sourceBase D he k hk room exceptional HD last z i n=
      sourceBase D he k hk room exceptional HD last z i n') : n=n' :=
  mark_unique (Nat.two_pow_pos _) (by decide : 0<2) hB
    (MersenneChronologicalMarks.sourceEuler he k 0 hk hB) _ _
    (source_sizes (hB:=hB) he k hk).1 hB3 hbeven (source_sizes (hB:=hB) he k hk).2 z hz n n' hn heq

/-- Original ordered physical mark list of the actual base, before cutting. -/
noncomputable def sourceWord (z : Fin (2)) (i : Fin (count (2*count m k) 0)) :
    List (VertexPower (VertexPower V k×VertexPower V k) 0×W) :=
  let E := MersenneChronologicalMarks.sourceEuler he k 0 hk hB
  (markPositions (Nat.two_pow_pos _) (by decide : 0<2) hB E.orbit E.length
    (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) hB) (by omega)) z).map
      (sourceBase D he k hk room exceptional HD last z i)

/-- Exact original chronological word lookup, retaining each actual source
factor and its canonical H assignment; no mark-order equality is assumed. -/
theorem source_word_lookup (z : Fin (2)) (f : Fin m) (q : Fin (2^(k+0+1))) :
    sourceWord D he k hk room exceptional HD last z
      (SourceFactors.index k 0 f (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q))=
    ZeroUpperChronologicalMarks.Actual.word he (D.cycles f).toClockData k hk room exceptional z hB
      (fun eps address=>((HamiltonCommonLast.normalize HD last).cycles
        (ZeroUpperFactors.association k 0 hk (SourceFactors.index k 0 f eps address))).toClockData) q := by
  unfold sourceWord ZeroUpperChronologicalMarks.Actual.word ZeroUpperChronologicalMarks.word markWord
  dsimp only
  rw [List.map_map]
  congr 1
  funext n
  unfold sourceBase base G H
  rw [ZeroUpperFactors.Actual.clock_eq D he k hk room exceptional z]
  rfl

end Source

/-- The two genuinely established global Mersenne incidence regimes. -/
inductive Branch : Nat→Nat→Type where
  | small (t : Nat) : Branch 2 (t+2)
  | large {e k : Nat} (he : 4≤e) (hk : 2≤k) : Branch e k

namespace Branch
theorem he {e k : Nat} : Branch e k→2≤e
  | .small _ => by decide
  | .large he _ => by omega
theorem hk {e k : Nat} : Branch e k→2≤k
  | .small _ => by omega
  | .large _ hk => hk
def exceptional {e k : Nat} : Branch e k→Bool
  | .small _ => true
  | .large _ _ => false
end Branch

section Global
variable {e d m B k : Nat} (br : Branch e k)
  (D : DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
  (room : 2^(k+0+3)∣lengthPower (2^e) k)
  (hB : 0<B) (hB4 : 4≤B) (evenB : B%2=0)
  (HD : DecompositionData (Vertex d) (@Adjacent d) (m*(2*2^(k+0-1))) B hB)
  (last : Vertex d) (z : Fin 2) (hz : 0<z.val)

noncomputable def assigned (f : Fin m) (eps : Bool) (address : Address (k+0)) :=
  ZeroUpperFactors.association k 0 br.hk (SourceFactors.index k 0 f eps address)

noncomputable def globalMarks : ChordGraph.Marks (ZeroUpperGlobalMarks.Physical e d k 0)
    (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=k) (h:=0))
    (m*2^(k+0+1)) (m*(2^(k+0)-1)) := by
  cases br with
  | small t =>
    exact ZeroUpperGlobalMarks.small_marks D t room hB hB4 evenB HD last
      (assigned (.small t)) z hz
  | large he hk =>
    exact ZeroUpperGlobalMarks.large_marks D he k hk room hB hB4 evenB HD last
      (assigned (.large he hk)) z hz

theorem global_word_lookup (f : Fin m) (q : Fin (2^(k+0+1))) :
    (globalMarks br D room hB hB4 evenB HD last z hz).word
      (positionEncode f q)=
    sourceWord D br.he k br.hk room br.exceptional HD last z
      (SourceFactors.index k 0 f (DenseSourceCounts.epsilonOf 1 q) (DenseSourceCounts.addressOf 1 q)) := by
  rw [source_word_lookup]
  cases br with
  | small t =>
    exact ZeroUpperGlobalMarks.small_word_lookup D t room hB hB4 evenB HD last
      (assigned (.small t)) z hz f q
  | large he hk =>
    exact ZeroUpperGlobalMarks.large_word_lookup D he k hk room hB hB4 evenB HD last
      (assigned (.large he hk)) z hz f q

theorem global_word_length (n : Fin (m*2^(k+0+1))) :
    4≤((globalMarks br D room hB hB4 evenB HD last z hz).word n).length := by
  cases br with
  | small t =>
    exact ZeroUpperGlobalMarks.small_word_length D t room hB hB4 evenB HD last
      (assigned (.small t)) z hz n
  | large he hk =>
    exact ZeroUpperGlobalMarks.large_word_length D he k hk room hB hB4 evenB HD last
      (assigned (.large he hk)) z hz n

noncomputable def globalSchedule : MarkSchedule.Data
    (globalMarks br D room hB hB4 evenB HD last z hz) :=
  Classical.choice (MarkSchedule.exists_data (SourceGlobalMarks.enumeration e d k 0)
    (globalMarks br D room hB hB4 evenB HD last z hz)
    (global_word_length br D room hB hB4 evenB HD last z hz))
end Global

structure Input where
  e : Nat
  d : Nat
  m : Nat
  B : Nat
  k : Nat
  branch : Branch e k
  hB : 0<B
  room : 2^(k+0+3)∣lengthPower (2^e) k
  D : DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e)
  HD : DecompositionData (Vertex d) (@Adjacent d) (m*(2*2^(k+0-1))) B hB
  last : Vertex d
  z : Fin 2
  hz : 0<z.val
  hB4 : 4≤B
  evenB : B%2=0

namespace Input
theorem he (I : Input) : 2≤I.e := I.branch.he
theorem hk (I : Input) : 2≤I.k := I.branch.hk
def exceptional (I : Input) : Bool := I.branch.exceptional
abbrev Y (I : Input) := SourceGlobalMarks.Physical I.e I.d I.k 0
def E (I : Input) : Nat := 2^(I.e*2^(I.k+0+1)-1)*I.B*(2^1+1)
theorem epos (I : Input) : 0<I.E := Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) I.hB) (by have := Nat.two_pow_pos 1; omega)
abbrev Index (I : Input) := Fin (I.m*2^(I.k+0+1))

noncomputable def assigned (I : Input) (f : Fin I.m) (eps : Bool) (address : Address (I.k+0)) :
    Fin (I.m*(2*2^(I.k+0-1))) :=
  ZeroUpperFactors.association I.k 0 I.hk (SourceFactors.index I.k 0 f eps address)

noncomputable def marks (I : Input) :=
  globalMarks I.branch I.D I.room I.hB I.hB4 I.evenB I.HD I.last I.z I.hz
noncomputable def schedule (I : Input) : MarkSchedule.Data I.marks :=
  globalSchedule I.branch I.D I.room I.hB I.hB4 I.evenB I.HD I.last I.z I.hz

def factor (I : Input) (n : I.Index) := ZeroUpperGlobalMarks.sourceIndex I.k 0 n
noncomputable def originalBase (I : Input) (n : I.Index) : Fin I.E→I.Y :=
  ZeroUpperAACBase.sourceBase I.D I.he I.k I.hk I.room
    I.exceptional I.HD I.last I.z (I.factor n)
noncomputable def originalColor (I : Input) : Fin I.E→Bool :=
  ZeroUpperAACBase.sourceColor (hB:=I.hB) I.he I.k I.hk I.z
noncomputable def originalFlag (I : Input) := cyclicFlag I.epos I.originalColor
noncomputable def originalWord (I : Input) (n : I.Index) : List I.Y :=
  ZeroUpperAACBase.sourceWord I.D I.he I.k I.hk I.room
    I.exceptional I.HD I.last I.z (I.factor n)

/-- The actual original source word is the literal ordered global word. -/
theorem word_lookup (I : Input) (n : I.Index) : I.originalWord n=I.marks.word n := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (I.k+0+1)) n
  have hn := AnchoredEmbedding.positionEncode_decode (Nat.two_pow_pos (I.k+0+1)) n
  change AnchoredEmbedding.positionEncode p.1 p.2=n at hn
  rw [←hn]
  unfold originalWord factor
  rw [ZeroUpperGlobalMarks.sourceIndex_lookup]
  exact (global_word_lookup I.branch I.D I.room I.hB I.hB4 I.evenB
    I.HD I.last I.z I.hz p.1 p.2).symm


theorem word_indices (I : Input) (n : I.Index) :
    I.originalWord n=(indices I.originalFlag).map (I.originalBase n) := rfl

theorem flag_card (I : Input) (n : I.Index) : Profile.cardinality I.originalFlag=(I.marks.word n).length := by
  rw [←word_lookup,word_indices,List.length_map,indices_length]

theorem flag_pos (I : Input) (n : I.Index) : 0<Profile.cardinality I.originalFlag := by
  have hlen := global_word_length I.branch I.D I.room I.hB I.hB4 I.evenB
    I.HD I.last I.z I.hz n
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
  apply ZeroUpperAACBase.source_mark_unique I.D I.he I.k I.hk I.room
    I.exceptional I.HD I.last (by have := I.hB4; omega) I.evenB I.z I.hz (I.factor n)
  · rw [I.flag_eq n] at hp
    exact hp
  · exact he

theorem collision (I : Input) (n : I.Index) (p q : Fin I.E) (he : I.base n p=I.base n q) :
    p=q ∨ I.color n p≠I.color n q := by
  have hh := ZeroUpperAACBase.source_collision I.D I.he I.k I.hk I.room
    I.exceptional I.HD I.last (by have := I.hB4; omega) I.evenB I.z I.hz (I.factor n) _ _ he
  exact hh.elim (fun he=>Or.inl (forward_injective I.epos (I.first n) he)) Or.inr

noncomputable def Host (I : Input) (n : I.Index) :=
  ZeroUpperFactors.Actual.Host I.D I.he I.k I.hk I.room I.exceptional
    (HamiltonCommonLast.normalize I.HD I.last) I.z (I.factor n)

theorem host_cover (I : Input) (n : I.Index) (x y : I.Y) : I.Host n x y ↔
    ∃p, SameEdge (I.base n p,I.base n (successor I.epos p)) (x,y) := by
  unfold Host
  rw [ZeroUpperAACBase.source_host_iff]
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
  apply ZeroUpperAACBase.source_edge_unique I.D I.he I.k I.hk I.room
    I.exceptional I.HD I.last (by have := I.hB4; omega) I.z (I.factor n)
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
theorem descriptor_card (I : Input) (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Profile.cardinality (I.flag n)=
      (LayerPartition.descriptors (cycles (I.schedule.active n)) cycles
        (I.schedule.inside n) (I.schedule.outside n)).length := by
  have hh := congrArg List.length (MarkSchedule.descriptor_order I.schedule cycles n)
  simp only [List.length_map,List.length_finRange] at hh
  exact (I.mark_card n).trans hh.symm

noncomputable def layers (I : Input) (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→PairedLayers.CycleData X R χ jR hj :=
  AACFoldEdgeLedger.forestLayers (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

noncomputable def selectors (I : Input) (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) : Fin (Profile.cardinality (I.flag n))→Bool :=
  AACFoldEdgeLedger.forestSelectors (I.flag n) (cycles (I.schedule.active n)) cycles
    (I.schedule.inside n) (I.schedule.outside n) (I.descriptor_card hj cycles n)

/-- The literal J cycle at every actual marked ordinal is precisely the
global palette label at the unchanged chronological word occurrence. -/
theorem layer_lookup (I : Input) (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj)
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

noncomputable def tour (I : Input) (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj)
    (n : I.Index) (color : Bool) : Fin (I.length (jR:=jR) n)→I.Y×X :=
  AACFoldClock.physical I.epos hj (I.base n) (I.color n) (cycles (I.schedule.active n))
    (I.layers hj cycles n) (I.selectors hj cycles n) color (I.qpos n)

/-- Actual two simple numeric tours and complete literal local input-host
partition. Geometry, descriptor size, return, schedule and coverage are all
derived from the actual source and the internally constructed global schedule. -/
theorem decomposition (I : Input) (h2 : 2≤jR)
    (cycles : Fin (I.m*(2^(I.k+0)-1))→PairedLayers.CycleData X R χ jR hj) (n : I.Index) :
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

theorem word_length (I : Input) (n : I.Index) :
    (I.marks.word n).length=
      (2*2^(I.k+0+1)-4)*(2^(I.e*2^(I.k+0+1)-1)/(2*2^(I.k+0+1)))*I.B := by
  rw [←I.flag_card n]
  exact AACPatternCardinality.source_long_cardinality I.he I.k 0 I.hk
    I.hB (by have := I.hB4; omega) I.evenB I.z I.hz

theorem fold_length (I : Input) (n : I.Index) (jR : Nat) :
    I.length (jR:=jR) n=jR*(I.E+
      (2*2^(I.k+0+1)-4)*(2^(I.e*2^(I.k+0+1)-1)/(2*2^(I.k+0+1)))*I.B) := by
  unfold length
  rw [AACFoldClock.length_eq I.epos (I.flag n) (I.cut_mark n) (I.qpos n),I.mark_card n,I.word_length n]

end Input
#print axioms Input.decomposition
#print axioms Input.word_cut
#print axioms Input.word_length
end ErdePaths.ZeroUpperAACBase
