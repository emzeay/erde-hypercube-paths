import ErdePaths.ChordGraph
import ErdePaths.LayerPartition

namespace ErdePaths.ChordSchedule

/-- Relabel actual occurrence brackets by their shared chord label. -/
def relabel {O Label : Type} {κ : O → Bool} (labels : O → Label) :
    NoncrossingMatch.Forest O κ → NoncrossingWord.Forest Label
  | .empty => .empty
  | .concat u v => .concat (relabel labels u) (relabel labels v)
  | .bracket x u _ _ => .bracket (labels x) (relabel labels u)

/-- Shared endpoint labels are proved at actual bracket edges, rather than
asserting an arbitrary layer word happens to cancel. -/
theorem relabel_flatten {O Label : Type} {κ : O → Bool} (labels : O → Label)
    (F : NoncrossingMatch.Forest O κ)
    (hlabels : ∀ e ∈ ChordGraph.chords F, labels e.1=labels e.2) :
    (relabel labels F).labels=F.flatten.map labels := by
  induction F with
  | empty => rfl
  | concat u v ihu ihv =>
    have hu : ∀ e ∈ ChordGraph.chords u, labels e.1=labels e.2 :=
      fun e he => hlabels e (List.mem_append_left _ he)
    have hv : ∀ e ∈ ChordGraph.chords v, labels e.1=labels e.2 :=
      fun e he => hlabels e (List.mem_append_right _ he)
    simp only [relabel,NoncrossingWord.Forest.labels,NoncrossingMatch.Forest.flatten,
      List.map_append,ihu hu,ihv hv]
  | bracket x u y h ih =>
    have hu : ∀ e ∈ ChordGraph.chords u, labels e.1=labels e.2 :=
      fun e he => hlabels e (List.mem_cons_of_mem _ he)
    have hxy : labels x=labels y := hlabels (x,y) (by simp [ChordGraph.chords])
    simp only [relabel,NoncrossingWord.Forest.labels,NoncrossingMatch.Forest.flatten,
      List.map_cons,List.map_append,List.map_nil,ih hu,hxy]

theorem relabel_pairs {O Label : Type} {κ : O → Bool} (labels : O → Label)
    (F : NoncrossingMatch.Forest O κ) : (relabel labels F).pairCount=F.pairCount := by
  induction F with
  | empty => rfl
  | concat u v ihu ihv => simp only [relabel,NoncrossingWord.Forest.pairCount,NoncrossingMatch.Forest.pairCount,ihu,ihv]
  | bracket x u y h ih => simp only [relabel,NoncrossingWord.Forest.pairCount,NoncrossingMatch.Forest.pairCount,ih]

private theorem labels_empty_of_zero {Label : Type} (F : NoncrossingWord.Forest Label)
    (hF : F.pairCount=0) : F.labels=[] := by
  have h := F.length_eq_twice_pairs
  rw [hF] at h
  cases he : F.labels with
  | nil => rfl
  | cons x xs => simp [he] at h

/-- Choose the first actual bracket as the active chord. The interior and
exterior passive forests preserve every endpoint's original order. -/
theorem active_split {Label : Type} (F : NoncrossingWord.Forest Label) (hF : 0<F.pairCount) :
    ∃ (a : Label) (inside outside : NoncrossingWord.Forest Label), F.labels=a::(inside.labels++a::outside.labels) ∧
      F.pairCount=inside.pairCount+outside.pairCount+1 := by
  induction F with
  | empty => simp [NoncrossingWord.Forest.pairCount] at hF
  | bracket a u ih =>
    exact ⟨a,u,.empty,by simp [NoncrossingWord.Forest.labels],by simp [NoncrossingWord.Forest.pairCount]⟩
  | concat u v ihu ihv =>
    by_cases hu : 0<u.pairCount
    · obtain ⟨a,inside,outside,he,hp⟩ := ihu hu
      refine ⟨a,inside,.concat outside v,?_,?_⟩
      · simp only [NoncrossingWord.Forest.labels,he,List.cons_append,List.append_assoc]
      · simp only [NoncrossingWord.Forest.pairCount,hp]
        omega
    · have huz : u.pairCount=0 := by omega
      have hv : 0<v.pairCount := by simpa only [NoncrossingWord.Forest.pairCount,huz,Nat.zero_add] using hF
      obtain ⟨a,inside,outside,he,hp⟩ := ihv hv
      refine ⟨a,inside,outside,?_,?_⟩
      · simp only [NoncrossingWord.Forest.labels,labels_empty_of_zero u huz,List.nil_append,he]
      · simpa only [NoncrossingWord.Forest.pairCount,huz,Nat.zero_add] using hp

/-- Balanced occurrence forests with shared chord labels supply the precise
active/passive schedule consumed by the checked common-host construction. -/
theorem occurrence_schedule {O Label : Type} {κ : O → Bool} (labels : O → Label)
    (F : NoncrossingMatch.Forest O κ) (hF : 2≤F.pairCount)
    (hlabels : ∀ e ∈ ChordGraph.chords F, labels e.1=labels e.2) :
    ∃ (a : Label) (inside outside : NoncrossingWord.Forest Label), F.flatten.map labels=a::(inside.labels++a::outside.labels) ∧
      1≤inside.pairCount+outside.pairCount := by
  have hf : 0<(relabel labels F).pairCount := by rw [relabel_pairs]; omega
  obtain ⟨a,inside,outside,he,hp⟩ := active_split (relabel labels F) hf
  refine ⟨a,inside,outside,?_,?_⟩
  · rw [←relabel_flatten labels F hlabels]
    exact he
  · rw [relabel_pairs] at hp
    omega

#print axioms relabel_flatten
#print axioms occurrence_schedule
end ErdePaths.ChordSchedule
