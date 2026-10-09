import ErdePaths.SourceMarkSize
import ErdePaths.MarkSchedule

namespace ErdePaths.SourceGlobalMarks
open SourceClock SourceProfile HierarchicalDecode DenseSourceCounts
attribute [local instance] Classical.propDecidable

/-- Literal initial-factor-major configuration order. -/
def pairs (m p : Nat) : List (Fin m × Fin p) :=
  (List.finRange m).flatMap fun f => (List.finRange p).map fun q => (f,q)

theorem pairs_mem {m p : Nat} (x : Fin m × Fin p) : x∈pairs m p := by
  exact List.mem_flatMap.mpr ⟨x.1,List.mem_finRange _,List.mem_map.mpr ⟨x.2,List.mem_finRange _,rfl⟩⟩

theorem pairs_nodup (m p : Nat) : (pairs m p).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro f hf
    exact List.Pairwise.map _ (fun q u hne he => hne (congrArg Prod.snd he)) (List.nodup_finRange p)
  · apply (List.nodup_finRange m).imp
    intro f g hne x hx y hy he
    obtain ⟨q,hq,hx⟩ := List.mem_map.mp hx
    obtain ⟨u,hu,hy⟩ := List.mem_map.mp hy
    exact hne (congrArg Prod.fst (hx.trans (he.trans hy.symm)))

theorem pair_encode_injective {m p : Nat} (hp : 0<p) :
    Function.Injective (fun x : Fin m × Fin p => AnchoredEmbedding.positionEncode x.1 x.2) := by
  intro x y he
  have hh := congrArg (AnchoredEmbedding.positionDecode hp) he
  simpa only [AnchoredEmbedding.positionDecode_encode] using hh

theorem pairs_encode_perm (m p : Nat) (hp : 0<p) :
    ((pairs m p).map (fun x => AnchoredEmbedding.positionEncode x.1 x.2)).Perm
      (List.finRange (m*p)) := by
  apply (List.perm_ext_iff_of_nodup
    (List.Pairwise.map _ (fun _ _ hne he => hne (pair_encode_injective hp he)) (pairs_nodup m p))
    (List.nodup_finRange _)).mpr
  intro n
  constructor
  · intro _; exact List.mem_finRange n
  · intro _
    exact List.mem_map.mpr ⟨AnchoredEmbedding.positionDecode hp n,pairs_mem _,
      AnchoredEmbedding.positionEncode_decode hp n⟩

private theorem sum_flatMap {X Y : Type} (l : List X) (f : X→List Y) (g : Y→Nat) :
    ((l.flatMap f).map g).sum=(l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

private theorem perm_sum {xs ys : List Nat} (h : xs.Perm ys) : xs.sum=ys.sum := by
  induction h with
  | nil => rfl
  | cons x h ih => simp only [List.sum_cons,ih]
  | swap x y xs => simp only [List.sum_cons]; omega
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- Exact factor/configuration sum transport through the numeric index. -/
theorem sum_decode (m p : Nat) (hp : 0<p) (g : Fin m→Fin p→Nat) :
    ((List.finRange (m*p)).map (fun n =>
      g (AnchoredEmbedding.positionDecode hp n).1 (AnchoredEmbedding.positionDecode hp n).2)).sum=
    ((List.finRange m).map fun f => ((List.finRange p).map (g f)).sum).sum := by
  have hh := (pairs_encode_perm m p hp).map (fun n =>
    g (AnchoredEmbedding.positionDecode hp n).1 (AnchoredEmbedding.positionDecode hp n).2)
  have hs := perm_sum hh
  rw [List.map_map] at hs
  simp only [Function.comp_def,AnchoredEmbedding.positionDecode_encode] at hs
  rw [←hs]
  rw [pairs,sum_flatMap]
  simp only [List.map_map,Function.comp_def]

/-- An actual aggregation operation; its degree is derived by exact finite
reindexing, with original words retained verbatim. -/
noncomputable def aggregate {V : Type} [DecidableEq V] {χ : V→Bool} {m p b : Nat}
    (hp : 0<p) (M : Fin m→ChordGraph.Marks V χ p b) : ChordGraph.Marks V χ (m*p) (m*b) where
  word n := (M (AnchoredEmbedding.positionDecode hp n).1).word (AnchoredEmbedding.positionDecode hp n).2
  balanced n := (M _).balanced _
  multiplicity v := by
    rw [sum_decode m p hp (fun f q => ((M f).word q).countP (fun x => decide (x=v)))]
    have hh := HallColor.constant_sum (List.finRange m) _ b (fun f _ => (M f).multiplicity v)
    simpa only [List.length_finRange,Nat.mul_comm] using hh

/-- The canonical lookup is a literal equality, not only a word permutation. -/
theorem aggregate_word {V : Type} [DecidableEq V] {χ : V→Bool} {m p b : Nat}
    (hp : 0<p) (M : Fin m→ChordGraph.Marks V χ p b) (f : Fin m) (q : Fin p) :
    (aggregate hp M).word (AnchoredEmbedding.positionEncode f q)=(M f).word q := by
  simp only [aggregate,AnchoredEmbedding.positionDecode_encode]

section Actual
variable {e d m M u B b : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
variable (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
variable (ho : ∀f address, Profile.cardinality (S f address)%2=1)
variable (hbalance : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r)) (hz : 0<z.val)
variable (hB : 0<B) (hB4 : 4≤B) (hbeven : B%2=0)
variable (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
variable (last : Vertex d) (assigned : Fin m→Bool→Address (a+h)→Fin M)
variable (hb : b<2^(a+h+1-r)) (hodd : b%2=1)

abbrev Physical (e d a h : Nat) :=
  VertexPower (VertexPower (Vertex e) a×VertexPower (Vertex e) a) h×Vertex d

/-- All initial-factor words, in genuine numeric factor/configuration order.
Balance and exact m*b-fold physical multiplicity are constructed. -/
noncomputable def marks :
    ChordGraph.Marks (Physical e d a h)
      (SourceChronologicalMarks.physicalParity (e:=e) (d:=d) (a:=a) (h:=h))
      (m*2^(a+h+1)) (m*b) :=
  aggregate (Nat.two_pow_pos _) (fun f =>
    SourceChronologicalMarks.marks D he a h r hr hh room hA S ho hbalance z
      hB (by omega) hbeven hz HD last (assigned f) hb hodd f)

/-- Canonical initial factor/configuration lookup survives aggregation
literally; the H-factor lookup is exactly the caller's actual assignment. -/
theorem word_lookup (f : Fin m) (q : Fin (2^(a+h+1))) :
    (marks D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd).word
      (AnchoredEmbedding.positionEncode f q)=
    SourceChronologicalMarks.word (b:=b) he (D.cycles f).toClockData a h r hr hh room hA
      (S f) (ho f) (hbalance f) z hB
      (fun eps address => ((HamiltonCommonLast.normalize HD last).cycles (assigned f eps address)).toClockData) q :=
  aggregate_word (Nat.two_pow_pos _) _ f q

/-- Every global word has an actual passive-pair size, derived uniformly. -/
theorem word_length (n : Fin (m*2^(a+h+1))) :
    4≤((marks D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd).word n).length := by
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (a+h+1)) n
  exact SourceMarkSize.source_word_length he (D.cycles p.1).toClockData a h r hr hh room hA
    (S p.1) (ho p.1) (hbalance p.1) z hz hB hB4 hbeven
    (fun eps address=>((HamiltonCommonLast.normalize HD last).cycles (assigned p.1 eps address)).toClockData)
    hb hodd p.2

end Actual

/-- Literal binary-coordinate encoding of the nested physical source host. -/
def encode {e d a h : Nat} (v : Physical e d a h) : Vertex (e*2^(a+h+1)+d) :=
  CubeProduct.encode ((CubeHierarchy.sourceIso e a h).encode v.1,v.2)

def decode {e d a h : Nat} (v : Vertex (e*2^(a+h+1)+d)) : Physical e d a h :=
  ((CubeHierarchy.sourceIso e a h).decode (CubeProduct.decode v).1,(CubeProduct.decode v).2)

theorem decode_encode {e d a h : Nat} (v : Physical e d a h) : decode (encode v)=v := by
  simp only [encode,decode,CubeProduct.decode_encode,CubeHierarchy.Coordinates.decode_encode]

theorem encode_decode {e d a h : Nat} (v : Vertex (e*2^(a+h+1)+d)) : encode (decode v)=v := by
  simp only [encode,decode,CubeHierarchy.Coordinates.encode_decode]
  exact CubeProduct.encode_decode v

/-- Actual finite enumeration is constructed through the checked binary
coordinate inverses; no finite-host enumeration premise is supplied. -/
def enumeration (e d a h : Nat) : ChordColor.Enumeration (Physical e d a h) where
  vertices := (List.finRange (2^(e*2^(a+h+1)+d))).map decode
  distinct := List.Pairwise.map _ (fun x y hne he => hne (by
    have hh := congrArg encode he
    simpa only [encode_decode] using hh)) (List.nodup_finRange _)
  covers v := List.mem_map.mpr ⟨encode v,List.mem_finRange _,decode_encode v⟩

section Palette
variable {e d m M u B b : Nat}
variable (D : HamiltonData.DecompositionData (Vertex e) (@Adjacent e) m (2^e) (Nat.two_pow_pos e))
variable (he : 2≤e) (a h r : Nat) (hr : r<a+h+1) (hh : 0<h)
variable (room : 2^(a+h+1)∣lengthPower (2^e) a) (hA : 2*u=2^r)
variable (S : Fin m→Address a→Fin (2^(e*2^a))→Bool)
variable (ho : ∀f address, Profile.cardinality (S f address)%2=1)
variable (hbalance : ∀f, ∀address : Address (a+h), Profile.prefixCount (S f (lowerAddress address)) (2*u)=u)
variable (z : Fin (2^r)) (hz : 0<z.val)
variable (hB : 0<B) (hB4 : 4≤B) (hbeven : B%2=0)
variable (HD : HamiltonData.DecompositionData (Vertex d) (@Adjacent d) M B hB)
variable (last : Vertex d) (assigned : Fin m→Bool→Address (a+h)→Fin M)
variable (hb : b<2^(a+h+1-r)) (hodd : b%2=1)

/-- Unconditional palette and literal noncrossing schedule for ALL actual
initial source factors. Neither global multiplicity nor labeling is assumed. -/
theorem exists_schedule : Nonempty (MarkSchedule.Data
    (marks D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd)) :=
  MarkSchedule.exists_data (enumeration e d a h)
    (marks D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd)
    (word_length D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd)

noncomputable def schedule : MarkSchedule.Data
    (marks D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd) :=
  Classical.choice (exists_schedule D he a h r hr hh room hA S ho hbalance z hz hB hB4 hbeven HD last assigned hb hodd)

end Palette
/-- Actual Hamilton-factor identity of each global chronological word. -/
def sourceIndex {m : Nat} (a h r : Nat) (n : Fin (m*2^(a+h+1))) :
    Fin (HamiltonTower.count (2*HamiltonTower.count m a) h) :=
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (a+h+1)) n
  SourceFactors.index a h p.1 (epsilonOf r p.2) (addressOf r p.2)

theorem sourceIndex_lookup {m : Nat} (a h r : Nat) (f : Fin m)
    (q : Fin (2^(a+h+1))) :
    sourceIndex a h r (AnchoredEmbedding.positionEncode f q)=
      SourceFactors.index a h f (epsilonOf r q) (addressOf r q) := by
  simp only [sourceIndex,AnchoredEmbedding.positionDecode_encode]

theorem sourceIndex_injective {m : Nat} (a h r : Nat) (hr : r<a+h+1) :
    Function.Injective (@sourceIndex m a h r) := by
  intro n n' he
  let p := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (a+h+1)) n
  let q := AnchoredEmbedding.positionDecode (Nat.two_pow_pos (a+h+1)) n'
  have hh := SourceFactors.index_injective a h p.1 q.1
    (epsilonOf r p.2) (epsilonOf r q.2) (addressOf r p.2) (addressOf r q.2) he
  have hq : p.2=q.2 := by
    rw [←code_of r hr p.2,←code_of r hr q.2,hh.2.1,hh.2.2]
  have hp : p=q := Prod.ext hh.1 hq
  have hi := congrArg (fun z : Fin m × Fin (2^(a+h+1)) =>
    AnchoredEmbedding.positionEncode z.1 z.2) hp
  simpa only [p,q,AnchoredEmbedding.positionEncode_decode] using hi

theorem sourceIndex_surjective {m : Nat} (a h r : Nat) (hr : r<a+h+1) :
    Function.Surjective (@sourceIndex m a h r) := by
  intro n
  obtain ⟨f,eps,address,he⟩ := SourceFactors.index_surjective a h n
  refine ⟨AnchoredEmbedding.positionEncode f (DenseSourceMarks.code r hr eps address),?_⟩
  rw [sourceIndex_lookup,epsilon_of_code,address_of_code]
  exact he

#print axioms sum_decode
#print axioms marks
#print axioms word_lookup
#print axioms word_length
#print axioms enumeration
#print axioms exists_schedule
#print axioms schedule
#print axioms sourceIndex_injective
#print axioms sourceIndex_surjective
end ErdePaths.SourceGlobalMarks
