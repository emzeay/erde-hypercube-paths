import ErdePaths.AACMarkExchange
import ErdePaths.AACMarkWord
import ErdePaths.CubeParity
import ErdePaths.NoncrossingMatch

namespace ErdePaths.AACPhysicalBalance
open SourceClock SquareLift AACTransition AACInduction AACMarkIntervals AACMarkExchange AACFine AACFineClock AACFineGeometry

def swapEnds {K : Nat} (hK : 1<K) (i : Fin K) : Fin K :=
  if i=⟨0,by omega⟩ then predecessor (by omega) ⟨0,by omega⟩
  else if i=predecessor (by omega) ⟨0,by omega⟩ then ⟨0,by omega⟩ else i

private theorem ends_ne {K} (hK : 1<K) :
    (⟨0,by omega⟩ : Fin K)≠predecessor (by omega) ⟨0,by omega⟩ := by
  intro hh
  have hs := congrArg (successor (by omega)) hh
  rw [AACMarkExchange.successor_zero hK,successor_predecessor] at hs
  have hv := congrArg Fin.val hs
  change 1=0 at hv
  omega

theorem swapEnds_involution {K} (hK : 1<K) (i : Fin K) : swapEnds hK (swapEnds hK i)=i := by
  by_cases h0 : i=⟨0,by omega⟩
  · subst i; simp [swapEnds,(ends_ne hK).symm]
  · by_cases hl : i=predecessor (by omega) ⟨0,by omega⟩
    · subst i; simp [swapEnds,(ends_ne hK).symm]
    · simp [swapEnds,h0,hl]

private theorem countP_swap {K} (hK : 1<K) (p : Fin K→Bool) :
    (List.finRange K).countP (fun i => p (swapEnds hK i))=(List.finRange K).countP p := by
  have hi : Function.Injective (swapEnds hK) := by
    intro x y he
    have hh := congrArg (swapEnds hK) he
    simpa only [swapEnds_involution] using hh
  have hn : ((List.finRange K).map (swapEnds hK)).Nodup := by
    apply List.pairwise_map.mpr
    apply (List.nodup_finRange K).imp
    intro x y hxy he; exact hxy (hi he)
  have hp : ((List.finRange K).map (swapEnds hK)).Perm (List.finRange K) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange K)).mpr
    intro i
    constructor
    · intro _; exact List.mem_finRange i
    · intro _
      exact List.mem_map.mpr ⟨swapEnds hK i,List.mem_finRange _,swapEnds_involution hK i⟩
  have hc := hp.countP_eq p
  simpa only [List.countP_map,Function.comp_def] using hc

/-- Exact per-row agreement count after ANY merge cutoff, derived by the
literal 0/predecessor0 transposition rather than assumed as balance. -/
theorem per_row_count {K B} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true) (n : Nat) (j : Fin B) :
    (List.finRange K).countP (fun i => decide (turnsAfter (by omega) t n (i,j)=
      turnsAfter (by omega) t n (successor (by omega) i,j)))=
    (List.finRange K).countP (fun i => decide (t i=t (successor (by omega) i))) := by
  by_cases hr : j.val<n
  · have he : (fun i : Fin K => decide (turnsAfter (by omega) t n (i,j)=
        turnsAfter (by omega) t n (successor (by omega) i,j)))=
      (fun i => decide (t (swapEnds hK i)=t (successor (by omega) (swapEnds hK i)))) := by
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rw [agreement_after hK t ht0 ht1 htlast]
      by_cases h0 : i=⟨0,by omega⟩
      · subst i; simp [swapEnds,ends_ne hK,hr,successor_predecessor,ht0,htlast]
      · by_cases hl : i=predecessor (by omega) ⟨0,by omega⟩
        · subst i; simp [swapEnds,(ends_ne hK).symm,hr,successor_zero hK,ht0,ht1]
        · simp [swapEnds,h0,hl,hr]
    rw [he]
    exact countP_swap hK (fun i => decide (t i=t (successor (by omega) i)))
  · apply List.countP_congr
    intro i hi
    simp [turnsAfter,hr]

/-- Every actual fine-grid mark has the threshold's first-axis parity when
A is even, including all predecessor replacements. -/
theorem marked_first_parity {K A B} (hK : 0<K) (hA : A%2=0) (turns : Grid K B→Bool)
    (z : Fin A) (v : Fine K A B) (hm : IsMark hK turns z v) : v.1.val%2=z.val%2 := by
  obtain ⟨i,j,rfl,hi⟩ := hm
  change (A*i.val+z.val)%2=z.val%2
  simp [Nat.add_mod,Nat.mul_mod,hA]

/-- The literal post-flip physical threshold list in one row. -/
def rowMarks {K A B : Nat} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A) (j : Fin B) :
    List (Fine K A B) :=
  ((List.finRange K).filter (fun i => decide (turns (i,j)=turns (successor hK i,j)))).map
    (fun i => (AnchoredEmbedding.positionEncode i z,j))

theorem rowMarks_length {K A B} (hK : 1<K) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (n : Nat) (z : Fin A) (j : Fin B) :
    (rowMarks (by omega) (turnsAfter (by omega) t n) z j).length=
      (List.finRange K).countP (fun i => decide (t i=t (successor (by omega) i))) := by
  simp only [rowMarks,List.length_map,←List.countP_eq_length_filter]
  exact per_row_count hK t ht0 ht1 htlast n j

theorem rowMarks_mem {K A B} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A)
    (j : Fin B) (v : Fine K A B) (hv : v∈rowMarks hK turns z j) :
    IsMark hK turns z v ∧ v.2=j := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hv
  have hh := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hh
  exact ⟨⟨i,j,rfl,hh⟩,rfl⟩

/-- Literal binary-cube parity of ANY actual fine-grid mark in genuine
product Hamilton clocks. Origin parities are retained, not normalized away. -/
theorem physical_mark_parity {n m K A B} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (F : HamiltonData.CycleData (Vertex n) (@Adjacent n) (K*A) (Nat.mul_pos hK hA))
    (H : HamiltonData.CycleData (Vertex m) (@Adjacent m) B hB)
    (ha : A%2=0) (turns : Grid K B→Bool) (z : Fin A) (v : Fine K A B)
    (hv : IsMark hK turns z v) :
    CubeParity.parity (CubeProduct.encode (F.cycle v.1,H.cycle v.2))=
      ((if z.val%2=0 then CubeParity.parity (F.cycle ⟨0,Nat.mul_pos hK hA⟩)
        else !CubeParity.parity (F.cycle ⟨0,Nat.mul_pos hK hA⟩)) ^^
       PairedLayers.flipN v.2.val (CubeParity.parity (H.cycle ⟨0,hB⟩))) := by
  rw [CubeParity.product_parity]
  change (CubeParity.parity (F.cycle v.1) ^^ CubeParity.parity (H.cycle v.2))=_
  rw [CubeParity.clock_parity (Nat.mul_pos hK hA) F v.1,CubeParity.clock_parity hB H v.2,
    AACUnfold.flipN_mod (v.1.val),marked_first_parity hK ha turns z v hv]

/-- Every row's explicit mark list has constant physical first-axis parity;
its product colors are the actual alternating second-axis cycle colors. -/
theorem rowMarks_physical_parity {n m K A B} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (F : HamiltonData.CycleData (Vertex n) (@Adjacent n) (K*A) (Nat.mul_pos hK hA))
    (H : HamiltonData.CycleData (Vertex m) (@Adjacent m) B hB)
    (ha : A%2=0) (turns : Grid K B→Bool) (z : Fin A) (j : Fin B)
    (v : Fine K A B) (hv : v∈rowMarks hK turns z j) :
    CubeParity.parity (CubeProduct.encode (F.cycle v.1,H.cycle v.2))=
      ((if z.val%2=0 then CubeParity.parity (F.cycle ⟨0,Nat.mul_pos hK hA⟩)
        else !CubeParity.parity (F.cycle ⟨0,Nat.mul_pos hK hA⟩)) ^^
       PairedLayers.flipN j.val (CubeParity.parity (H.cycle ⟨0,hB⟩))) := by
  have hm := rowMarks_mem hK turns z j v hv
  have hh := physical_mark_parity hK hA hB F H ha turns z v hm.1
  simpa only [hm.2] using hh

private theorem constant_count {V} (χ : V→Bool) (xs : List V) (c : Bool)
    (hc : ∀v∈xs, χ v=c) : xs.countP χ=xs.length*c.toNat := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hc x (by simp)
    have ht := ih (fun v hv => hc v (by simp [hv]))
    cases c <;> simp [hx,ht]

/-- Equal-sized explicit rows with opposite actual colors have a balanced
combined physical word; this does not assume a balanced mark word. -/
theorem balanced_opposite_rows {V} (χ : V→Bool) (xs ys : List V) (c : Bool)
    (hx : ∀v∈xs, χ v=c) (hy : ∀v∈ys, χ v= !c) (hl : xs.length=ys.length) :
    NoncrossingMatch.Balanced χ (xs++ys) := by
  unfold NoncrossingMatch.Balanced
  rw [List.countP_append,List.countP_append,
    constant_count χ xs c hx,constant_count χ ys (!c) hy]
  have hx' : ∀v∈xs, (!χ v)= !c := fun v hv => congrArg Bool.not (hx v hv)
  have hy' : ∀v∈ys, (!χ v)=c := by
    intro v hv; rw [hy v hv,Bool.not_not]
  rw [constant_count (fun v => !χ v) xs (!c) hx',constant_count (fun v => !χ v) ys c hy',hl]
  omega

/-- The physical word for one literal post-flip row. -/
def physicalRow {n m K A B} (F : ClockData (Vertex n) (K*A)) (H : ClockData (Vertex m) B)
    (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A) (j : Fin B) : List (Vertex (n+m)) :=
  (rowMarks hK turns z j).map (fun v => CubeProduct.encode (F.cycle v.1,H.cycle v.2))

/-- An actual adjacent pair of post-flip rows is balanced, for every merge
cutoff, even subdivision length and genuine binary-cube cycle clocks. -/
theorem adjacent_rows_balanced {n m K A B} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (F : HamiltonData.CycleData (Vertex n) (@Adjacent n) (K*A) (Nat.mul_pos (by omega) hA))
    (H : HamiltonData.CycleData (Vertex m) (@Adjacent m) B hB)
    (ha : A%2=0) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (cutoff : Nat) (z : Fin A) (j : Fin B) :
    NoncrossingMatch.Balanced CubeParity.parity
      (physicalRow F.toClockData H.toClockData (by omega) (turnsAfter (by omega) t cutoff) z j ++
       physicalRow F.toClockData H.toClockData (by omega) (turnsAfter (by omega) t cutoff) z (successor hB j)) := by
  let α := if z.val%2=0 then CubeParity.parity (F.cycle ⟨0,Nat.mul_pos (by omega) hA⟩) else !CubeParity.parity (F.cycle ⟨0,Nat.mul_pos (by omega) hA⟩)
  let c := α ^^ CubeParity.parity (H.cycle j)
  apply balanced_opposite_rows _ _ _ c
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    have hh := rowMarks_physical_parity (by omega) hA hB F H ha _ z j x hx
    rw [←CubeParity.clock_parity hB H j] at hh
    exact hh
  · intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    have hh := rowMarks_physical_parity (by omega) hA hB F H ha _ z (successor hB j) x hx
    rw [←CubeParity.clock_parity hB H (successor hB j),CubeParity.adjacent_flips (H.adjacent j)] at hh
    have he : (α ^^ !CubeParity.parity (H.cycle j))= !c := by
      dsimp only [c]; cases α <;> cases CubeParity.parity (H.cycle j) <;> rfl
    exact hh.trans he
  · simp only [physicalRow,List.length_map]
    rw [rowMarks_length hK t ht0 ht1 htlast cutoff z j,
      rowMarks_length hK t ht0 ht1 htlast cutoff z (successor hB j)]

private theorem balanced_flatMap {I V} (χ : V→Bool) (is : List I) (word : I→List V)
    (hb : ∀i∈is, NoncrossingMatch.Balanced χ (word i)) :
    NoncrossingMatch.Balanced χ (is.flatMap word) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := hb i (by simp)
    have ht := ih (fun j hj => hb j (by simp [hj]))
    unfold NoncrossingMatch.Balanced at hi ht ⊢
    simp only [List.flatMap_cons,List.countP_append,hi,ht]

/-- Explicit row-pair enumeration of physical post-flip marks. Pairing rows
is only an enumeration for counting; it does not prescribe tour order. -/
def pairedRowWord {n m K A B} (F : ClockData (Vertex n) (K*A)) (H : ClockData (Vertex m) B)
    (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool) (z : Fin A) : List (Vertex (n+m)) :=
  (List.finRange (B/2)).flatMap (fun k =>
    let j : Fin B := ⟨2*k.val,by have := k.isLt; omega⟩
    physicalRow F H hK turns z j ++ physicalRow F H hK turns z (successor hB j))

/-- Complete balance of the concrete paired-row enumeration, derived from
actual clock parities and literal merge count preservation. -/
theorem pairedRowWord_balanced {n m K A B} (hK : 1<K) (hA : 0<A) (hB : 0<B)
    (F : HamiltonData.CycleData (Vertex n) (@Adjacent n) (K*A) (Nat.mul_pos (by omega) hA))
    (H : HamiltonData.CycleData (Vertex m) (@Adjacent m) B hB)
    (ha : A%2=0) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (cutoff : Nat) (z : Fin A) :
    NoncrossingMatch.Balanced CubeParity.parity
      (pairedRowWord F.toClockData H.toClockData (by omega) hB (turnsAfter (by omega) t cutoff) z) := by
  apply balanced_flatMap
  intro k hk
  exact adjacent_rows_balanced hK hA hB F H ha t ht0 ht1 htlast cutoff z _

theorem rowMarks_mem_iff {K A B} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A)
    (j : Fin B) (v : Fine K A B) : v∈rowMarks hK turns z j ↔ IsMark hK turns z v ∧ v.2=j := by
  constructor
  · exact rowMarks_mem hK turns z j v
  · rintro ⟨⟨i,j',hv,hm⟩,hj⟩
    have hj' : j'=j := by simpa only [hv] using hj
    subst j'
    apply List.mem_map.mpr
    refine ⟨i,List.mem_filter.mpr ⟨List.mem_finRange i,by simpa using hm⟩,hv.symm⟩

theorem rowMarks_nodup {K A B} (hK : 0<K) (turns : Grid K B→Bool) (z : Fin A) (j : Fin B) :
    (rowMarks hK turns z j).Nodup := by
  apply List.pairwise_map.mpr
  apply ((List.nodup_finRange K).filter _).imp
  intro i i' hne he
  have hp := @point_injective K A B z (i,j) (i',j) he
  exact hne (Prod.mk.inj hp).1

def evenRow {B : Nat} (k : Fin (B/2)) : Fin B := ⟨2*k.val,by have := k.isLt; omega⟩

private theorem evenRow_next {B} (hB : 0<B) (k : Fin (B/2)) :
    (successor hB (evenRow k)).val=2*k.val+1 := by
  change (2*k.val+1)%B=2*k.val+1
  exact Nat.mod_eq_of_lt (by have := k.isLt; omega)

def rowBlock {K A B} (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool) (z : Fin A)
    (k : Fin (B/2)) : List (Fine K A B) :=
  rowMarks hK turns z (evenRow k) ++ rowMarks hK turns z (successor hB (evenRow k))

def pairedFineWord {K A B} (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool) (z : Fin A) :
    List (Fine K A B) := (List.finRange (B/2)).flatMap (rowBlock hK hB turns z)

private theorem block_row {K A B} (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool)
    (z : Fin A) (k : Fin (B/2)) (v : Fine K A B) (hv : v∈rowBlock hK hB turns z k) :
    v.2.val/2=k.val := by
  rcases List.mem_append.mp hv with hv|hv
  · have hj := (rowMarks_mem hK turns z _ v hv).2
    rw [hj]; change (2*k.val)/2=k.val
    omega
  · have hj := (rowMarks_mem hK turns z _ v hv).2
    rw [hj,evenRow_next]; omega

private theorem rowBlock_nodup {K A B} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B→Bool) (z : Fin A) (k : Fin (B/2)) :
    (rowBlock hK hB turns z k).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨rowMarks_nodup _ _ _ _,rowMarks_nodup _ _ _ _,?_⟩
  intro v hv w hw he
  have hvj := (rowMarks_mem hK turns z _ v hv).2
  have hwj := (rowMarks_mem hK turns z _ w hw).2
  have hh : evenRow k=successor hB (evenRow k) := hvj.symm.trans ((congrArg Prod.snd he).trans hwj)
  have hn := congrArg Fin.val hh
  rw [evenRow_next] at hn
  change 2*k.val=2*k.val+1 at hn
  omega

theorem pairedFineWord_nodup {K A B} (hK : 0<K) (hB : 0<B)
    (turns : Grid K B→Bool) (z : Fin A) : (pairedFineWord hK hB turns z).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k hk; exact rowBlock_nodup hK hB turns z k
  · apply (List.nodup_finRange (B/2)).imp
    intro k l hne v hv w hw he
    have hk := block_row hK hB turns z k v hv
    have hl := block_row hK hB turns z l w hw
    rw [he,hl] at hk
    exact hne (Fin.ext hk.symm)

theorem pairedFineWord_mem_iff {K A B} (hK : 0<K) (hB : 0<B) (hb : B%2=0)
    (turns : Grid K B→Bool) (z : Fin A) (v : Fine K A B) :
    v∈pairedFineWord hK hB turns z ↔ IsMark hK turns z v := by
  constructor
  · intro hv
    obtain ⟨k,hk,hv⟩ := List.mem_flatMap.mp hv
    rcases List.mem_append.mp hv with hv|hv
    · exact (rowMarks_mem hK turns z _ v hv).1
    · exact (rowMarks_mem hK turns z _ v hv).1
  · intro hm
    let k : Fin (B/2) := ⟨v.2.val/2,by have := v.2.isLt; omega⟩
    apply List.mem_flatMap.mpr
    refine ⟨k,List.mem_finRange k,?_⟩
    apply List.mem_append.mpr
    by_cases he : v.2.val%2=0
    · left; apply (rowMarks_mem_iff hK turns z _ v).mpr
      refine ⟨hm,?_⟩
      apply Fin.ext; change v.2.val=2*(v.2.val/2); omega
    · right; apply (rowMarks_mem_iff hK turns z _ v).mpr
      refine ⟨hm,?_⟩
      apply Fin.ext; rw [evenRow_next]
      change v.2.val=2*(v.2.val/2)+1
      have := Nat.mod_lt v.2.val (by decide : 0<2)
      omega

theorem pairedRowWord_eq_map {n m K A B} (F : ClockData (Vertex n) (K*A))
    (H : ClockData (Vertex m) B) (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool) (z : Fin A) :
    pairedRowWord F H hK hB turns z=(pairedFineWord hK hB turns z).map
      (fun v => CubeProduct.encode (F.cycle v.1,H.cycle v.2)) := by
  simp only [pairedRowWord,pairedFineWord,List.map_flatMap,rowBlock,List.map_append,physicalRow,evenRow]

private theorem embedded_injective {n m K A B} (F : ClockData (Vertex n) (K*A))
    (H : ClockData (Vertex m) B) :
    Function.Injective (fun v : Fine K A B => CubeProduct.encode (F.cycle v.1,H.cycle v.2)) := by
  intro v w he
  have hp : physical F H v=physical F H w := CubeProduct.encode_injective he
  exact physical_injective F H hp

theorem pairedRowWord_nodup {n m K A B} (F : ClockData (Vertex n) (K*A))
    (H : ClockData (Vertex m) B) (hK : 0<K) (hB : 0<B) (turns : Grid K B→Bool) (z : Fin A) :
    (pairedRowWord F H hK hB turns z).Nodup := by
  rw [pairedRowWord_eq_map]
  apply List.pairwise_map.mpr
  apply (pairedFineWord_nodup hK hB turns z).imp
  intro v w hne he
  exact hne (embedded_injective F H he)

/-- Exact membership of the explicit PHYSICAL mark enumeration on actual
binary product vertices, with its literal inverse factor coordinates. -/
theorem pairedRowWord_mem_iff {n m K A B} (F : ClockData (Vertex n) (K*A))
    (H : ClockData (Vertex m) B) (hK : 0<K) (hB : 0<B) (hb : B%2=0)
    (turns : Grid K B→Bool) (z : Fin A) (v : Vertex (n+m)) :
    v∈pairedRowWord F H hK hB turns z ↔
      IsMark hK turns z (F.position (CubeProduct.decode v).1,H.position (CubeProduct.decode v).2) := by
  rw [pairedRowWord_eq_map]
  constructor
  · intro hm
    obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    have hp := congrArg CubeProduct.decode he
    rw [CubeProduct.decode_encode] at hp
    have hh := congrArg (fun p : Vertex n×Vertex m => (F.position p.1,H.position p.2)) hp
    simp only [F.position_cycle,H.position_cycle] at hh
    rw [←hh]
    exact (pairedFineWord_mem_iff hK hB hb turns z x).mp hx
  · intro hm
    refine List.mem_map.mpr ⟨(F.position (CubeProduct.decode v).1,H.position (CubeProduct.decode v).2),?_,?_⟩
    · exact (pairedFineWord_mem_iff hK hB hb turns z _).mpr hm
    · simp only [F.cycle_position,H.cycle_position]
      exact CubeProduct.encode_decode v

/-- The chronological Euler mark word and the row-pair word enumerate the
same actual degree-two marks, each once. -/
theorem chronological_perm {K A B N E : Nat} (hK : 0<K) (hA : 0<A) (hB : 0<B)
    (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0) {hN : 0<N} {turns : Grid K B→Bool}
    (C : AACMerge.Orbit (State K B) (transition hK hB turns) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel hK hA hB C hE))
    (hsur : Function.Surjective (fineLabel hK hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    (markWord hK hA hB C hE hpos z).Perm (pairedFineWord hK hB turns z) := by
  apply (List.perm_ext_iff_of_nodup
    (markWord_nodup hK hA hB h3 hB3 hb C hE hpos hE2 hinj z hz)
    (pairedFineWord_nodup hK hB turns z)).mpr
  intro v
  rw [AACMarkWord.mem_word_iff hK hA hB hb C hE hpos hsur z hz,
    pairedFineWord_mem_iff hK hB hb turns z]

/-- Balance of the ACTUAL chronological physical Euler mark word, derived
from actual graph-cycle parity, merge count preservation and exact mark
uniqueness. No balanced-mark hypothesis or chronological reordering premise. -/
theorem chronological_physical_balanced {n m K A B N E : Nat}
    (hK : 1<K) (hA : 0<A) (hB : 0<B) (h3 : 3≤K*A) (hB3 : 3≤B) (hb : B%2=0)
    (F : HamiltonData.CycleData (Vertex n) (@Adjacent n) (K*A) (Nat.mul_pos (by omega) hA))
    (H : HamiltonData.CycleData (Vertex m) (@Adjacent m) B hB)
    (ha : A%2=0) (t : Fin K→Bool)
    (ht0 : t ⟨0,by omega⟩=false) (ht1 : t ⟨1,hK⟩=false)
    (htlast : t (predecessor (by omega) ⟨0,by omega⟩)=true)
    (cutoff : Nat) {hN : 0<N}
    (C : AACMerge.Orbit (State K B) (transition (by omega) hB (turnsAfter (by omega) t cutoff)) N hN)
    (hE : (indexList (A:=A) C).length=E) (hpos : 0<E) (hE2 : 2≤E)
    (hinj : Function.Injective (fineLabel (by omega) hA hB C hE))
    (hsur : Function.Surjective (fineLabel (by omega) hA hB C hE)) (z : Fin A) (hz : 0<z.val) :
    NoncrossingMatch.Balanced CubeParity.parity
      ((markWord (by omega) hA hB C hE hpos z).map
        (fun v => CubeProduct.encode (F.cycle v.1,H.cycle v.2))) := by
  have hp := (chronological_perm (by omega) hA hB h3 hB3 hb C hE hpos hE2 hinj hsur z hz).map
    (fun v => CubeProduct.encode (F.cycle v.1,H.cycle v.2))
  have hbalance := pairedRowWord_balanced hK hA hB F H ha t ht0 ht1 htlast cutoff z
  rw [pairedRowWord_eq_map] at hbalance
  unfold NoncrossingMatch.Balanced at hbalance ⊢
  rw [hp.countP_eq CubeParity.parity,hp.countP_eq (fun v => !CubeParity.parity v)]
  exact hbalance

#print axioms pairedRowWord_mem_iff
#print axioms pairedRowWord_nodup
#print axioms chronological_perm
#print axioms chronological_physical_balanced
#print axioms pairedFineWord_mem_iff
#print axioms pairedFineWord_nodup
#print axioms pairedRowWord_balanced
#print axioms adjacent_rows_balanced
#print axioms physical_mark_parity
#print axioms rowMarks_length
#print axioms per_row_count
#print axioms marked_first_parity
end ErdePaths.AACPhysicalBalance
