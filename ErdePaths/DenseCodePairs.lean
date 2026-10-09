import ErdePaths.DenseSourceCounts

namespace ErdePaths.DenseCodePairs
open DenseSourceMarks DenseSourceCounts HierarchicalDecode

/-- Actual numerical addresses, with each literal false/true code adjacent. -/
noncomputable def pairs {K : Nat} (r : Nat) (hr : r<K+1) : List (Vertex (K+1)) :=
  (List.finRange (2^K)).flatMap fun a =>
    [code r hr false (binaryTuple a),code r hr true (binaryTuple a)]

/-- The existing actual source-bit inverse separates both the address and
profile bit of every code. -/
theorem code_pair_injective {K : Nat} (r : Nat) (hr : r<K+1)
    (a b : Vertex K) (epsilon delta : Bool)
    (he : code r hr epsilon (binaryTuple a)=code r hr delta (binaryTuple b)) :
    a=b ∧ epsilon=delta := by
  have ha := congrArg (addressOf r) he
  rw [address_of_code,address_of_code] at ha
  have hb := congrArg (epsilonOf r) he
  rw [epsilon_of_code,epsilon_of_code] at hb
  exact ⟨binaryTuple_injective ha,hb⟩

theorem pairs_nodup {K : Nat} (r : Nat) (hr : r<K+1) : (pairs r hr).Nodup := by
  unfold pairs
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    have hh : code r hr false (binaryTuple a)≠code r hr true (binaryTuple a) := by
      intro he
      have hp := (code_pair_injective r hr a a false true he).2
      cases hp
    simp [hh]
  · apply (List.nodup_finRange (2^K)).imp
    intro a b hab x hx y hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      intro he <;> exact hab (code_pair_injective r hr _ _ _ _ he).1

/-- Every bounded full-width code occurs, from its actual inverse profile bit
and inverse source address. No representative-cover premise is assumed. -/
theorem mem_pairs {K : Nat} (r : Nat) (hr : r<K+1) (q : Vertex (K+1)) : q∈pairs r hr := by
  obtain ⟨a,ha⟩ := binaryTuple_surjective (addressOf r q)
  apply List.mem_flatMap.mpr
  refine ⟨a,List.mem_finRange a,?_⟩
  have hc := code_of r hr q
  rw [←ha] at hc
  cases he : epsilonOf r q
  · rw [he] at hc
    exact List.mem_cons.mpr (Or.inl hc.symm)
  · rw [he] at hc
    exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr hc.symm))

/-- The paired list is a permutation of the complete literal numeric range. -/
theorem pairs_perm {K : Nat} (r : Nat) (hr : r<K+1) :
    (pairs r hr).Perm (List.finRange (2^(K+1))) := by
  apply (List.perm_ext_iff_of_nodup (pairs_nodup r hr) (List.nodup_finRange _)).mpr
  intro q
  exact ⟨fun _ => List.mem_finRange q,fun _ => mem_pairs r hr q⟩

private theorem sum_pair_blocks {X Y : Type} (l : List X) (f g : X→Y) (F : Y→Nat) :
    ((l.flatMap fun a => [f a,g a]).map F).sum=
      (l.map (fun a => F (f a)+F (g a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_cons,List.map_nil,
      List.sum_append,List.sum_cons,List.sum_nil,ih]
    omega

/-- Arbitrary numeric configuration sums aggregate as actual reciprocal
pairs, without a grouping or cover hypothesis. -/
theorem sum_codes {K : Nat} (r : Nat) (hr : r<K+1) (F : Vertex (K+1)→Nat) :
    ((List.finRange (2^(K+1))).map F).sum=
      ((List.finRange (2^K)).map (fun a =>
        F (code r hr false (binaryTuple a))+F (code r hr true (binaryTuple a)))).sum := by
  have hp := List.Perm.sum_nat ((pairs_perm r hr).map F)
  rw [←hp]
  exact sum_pair_blocks _ _ _ _

/-- Literal decoding of full numeric configurations has exactly the paired
sum, using the actual inverse address/profile-bit laws. -/
theorem sum_configurations {K : Nat} (r : Nat) (hr : r<K+1)
    (F : Bool→Address K→Nat) :
    ((List.finRange (2^(K+1))).map (fun q=>F (epsilonOf r q) (addressOf r q))).sum=
      ((List.finRange (2^K)).map (fun a=>F false (binaryTuple a)+F true (binaryTuple a))).sum := by
  simpa only [epsilon_of_code,address_of_code] using
    sum_codes r hr (fun q=>F (epsilonOf r q) (addressOf r q))

/-- Pointwise reciprocal pair preservation aggregates over all actual
numeric configurations, with neither a group-cover nor global-count premise. -/
theorem aggregate_exchange {K : Nat} (r : Nat) (hr : r<K+1)
    (F G : Bool→Address K→Nat)
    (hp : ∀a, F false a+F true a=G false a+G true a) :
    ((List.finRange (2^(K+1))).map (fun q=>F (epsilonOf r q) (addressOf r q))).sum=
      ((List.finRange (2^(K+1))).map (fun q=>G (epsilonOf r q) (addressOf r q))).sum := by
  rw [sum_configurations r hr F,sum_configurations r hr G]
  have hf : (fun a : Vertex K=>F false (binaryTuple a)+F true (binaryTuple a))=
      (fun a=>G false (binaryTuple a)+G true (binaryTuple a)) :=
    funext (fun a=>hp (binaryTuple a))
  rw [hf]

#print axioms aggregate_exchange
#print axioms pairs_nodup
#print axioms pairs_perm
#print axioms sum_codes
end ErdePaths.DenseCodePairs
