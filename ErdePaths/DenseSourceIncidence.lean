import ErdePaths.DenseSourceCounts

namespace ErdePaths.DenseSourceIncidence
open SourceClock SourceProfile HierarchicalDecode DenseSourceMarks DenseSourceCounts
attribute [local instance] Classical.propDecidable

private theorem sum_indicators {X : Type} (l : List X) (p : X→Prop) :
    (l.map (fun x=>if p x then 1 else 0)).sum=l.countP (fun x=>decide (p x)) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons,List.sum_cons,List.countP_cons,ih]; split <;> simp_all <;> omega

/-- A bounded configuration contains a physical vertex at most once across
its literal residue classes. Thus its canonical list count is true incidence. -/
theorem configuration_incidence {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1) (direction : Bool→Address (k+h)→Bool)
    (epsilon : Bool) (address : Address (k+h)) (b : Nat) (hb : b≤2^(k+h+1-r))
    (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    (configurationList he C k h r hr S ho direction epsilon address b).countP (fun w=>decide (w=v))=
      if ∃u : Fin b, Marked he C k h r hr S ho direction epsilon address u.val v then 1 else 0 := by
  rw [configurationList,List.countP_flatMap]
  have hf : (fun u : Fin b=> (markedVertices he C k h r hr S ho direction epsilon address u.val).countP
      (fun w=>decide (w=v)))=
      (fun u=>if Marked he C k h r hr S ho direction epsilon address u.val v then 1 else 0) := by
    funext u
    exact marked_list_count he C k h r hr S ho direction epsilon address u.val v
  change ((List.finRange b).map _).sum=_
  simp only [Function.comp_def]
  rw [hf,sum_indicators]
  by_cases hm : ∃u : Fin b, Marked he C k h r hr S ho direction epsilon address u.val v
  · rw [ite_eq_left hm]
    obtain ⟨owner,howner⟩ := hm
    have hp (u : Fin b) : Marked he C k h r hr S ho direction epsilon address u.val v ↔ u=owner := by
      constructor
      · intro hu
        apply Fin.ext
        exact marked_offset_unique he C k h r hr S ho direction
          epsilon address u.val owner.val (by have := u.isLt; omega) (by have := owner.isLt; omega) v hu howner
      · intro hu; subst u; exact howner
    have hpred : (fun u : Fin b=>decide (Marked he C k h r hr S ho
      direction epsilon address u.val v))=(fun u=>u==owner) := by
      funext u
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,beq_iff_eq,hp]
    rw [hpred,←List.count_eq_countP]
    simpa only [List.mem_finRange,ite_true] using (List.nodup_finRange b).count (a:=owner)
  · rw [ite_eq_right hm]
    have hpred : (fun u : Fin b=>decide (Marked he C k h r hr S ho direction epsilon address u.val v))=
      (fun _=>false) := by
      funext u
      exact decide_eq_false (fun hu=>hm ⟨u,hu⟩)
    rw [hpred,List.countP_false]
    rfl

/-- Full actual joint-source ownership yields b-fold incidence of bounded
configuration mark unions, not merely a count with duplicate appearances. -/
theorem exact_configuration_incidence {V : Type} {e : Nat} (he : 2≤e) (C : ClockData V (2^e))
    (k h r : Nat) (hr : r<k+h+1) (S : Address k→Fin (2^(e*2^k))→Bool)
    (ho : ∀ a, Profile.cardinality (S a)%2=1)
    (room : 2^(k+h+1)∣lengthPower (2^e) k) (direction : Bool→Address (k+h)→Bool)
    (depends : ∀d a a', AgreeBelow r a a'→direction d a=direction d a')
    (b : Nat) (hb : b≤2^(k+h+1-r)) (v : VertexPower (VertexPower V k×VertexPower V k) h) :
    ((List.finRange (2^(k+h+1))).map (fun q=>
      if ∃u : Fin b, Marked he C k h r hr S ho direction
        (epsilonOf r q) (addressOf r q) u.val v then 1 else 0)).sum=b := by
  have hh := configuration_multiplicity he C k h r hr S ho room direction depends b v
  have hf : (fun q : Fin (2^(k+h+1))=>
      (configurationList he C k h r hr S ho direction (epsilonOf r q) (addressOf r q) b).countP
        (fun w=>decide (w=v)))=(fun q=>if ∃u : Fin b, Marked he C k h r hr S ho direction
          (epsilonOf r q) (addressOf r q) u.val v then 1 else 0) := by
    funext q
    exact configuration_incidence he C k h r hr S ho direction _ _ b hb v
  rw [hf] at hh
  exact hh

#print axioms exact_configuration_incidence
#print axioms configuration_incidence
end ErdePaths.DenseSourceIncidence
