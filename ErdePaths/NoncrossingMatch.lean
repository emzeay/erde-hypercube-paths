import Std

namespace ErdePaths.NoncrossingMatch

/-- Actual endpoints remain in their original linear order. -/
inductive Forest (V : Type) (χ : V → Bool) where
  | empty : Forest V χ
  | concat : Forest V χ → Forest V χ → Forest V χ
  | bracket (x : V) (inside : Forest V χ) (y : V) (opposite : χ x ≠ χ y) : Forest V χ

def Forest.flatten {V : Type} {χ : V → Bool} : Forest V χ → List V
  | .empty => []
  | .concat u v => u.flatten ++ v.flatten
  | .bracket x u y _ => x :: (u.flatten ++ [y])

/-- Insert a new adjacent opposite pair at a chosen gap. -/
theorem Forest.insert_pair {V : Type} {χ : V → Bool}
    (F : Forest V χ) (x y : V) (hxy : χ x ≠ χ y) (k : Nat) :
    ∃ G : Forest V χ,
      G.flatten = F.flatten.take k ++ [x,y] ++ F.flatten.drop k := by
  induction F generalizing k with
  | empty => exact ⟨.bracket x .empty y hxy, by simp [flatten]⟩
  | concat u v ihu ihv =>
    by_cases hk : k ≤ u.flatten.length
    · obtain ⟨g,hg⟩ := ihu k
      refine ⟨.concat g v,?_⟩
      simp only [flatten,hg,List.take_append_of_le_length hk,List.drop_append_of_le_length hk,
        List.append_assoc]
    · obtain ⟨g,hg⟩ := ihv (k-u.flatten.length)
      refine ⟨.concat u g,?_⟩
      have hu : u.flatten.length ≤ k := by omega
      simp only [flatten,hg,List.take_append,List.drop_append,List.take_of_length_le hu,
        List.drop_eq_nil_of_le hu,List.nil_append,List.append_assoc]
  | bracket a u b hab ihu =>
    cases k with
    | zero => exact ⟨.concat (.bracket x .empty y hxy) (.bracket a u b hab),by simp [flatten]⟩
    | succ k =>
      by_cases hk : k ≤ u.flatten.length
      · obtain ⟨g,hg⟩ := ihu k
        refine ⟨.bracket a g b hab,?_⟩
        simp only [flatten,hg,List.take_succ_cons,List.drop_succ_cons,
          List.take_append_of_le_length hk,List.drop_append_of_le_length hk,List.append_assoc,
          List.cons_append]
      · have hlen : (a :: (u.flatten ++ [b])).length ≤ k+1 := by simp only [List.length_cons,List.length_append,List.length_nil]; omega
        refine ⟨.concat (.bracket a u b hab) (.bracket x .empty y hxy),?_⟩
        simp [flatten,List.take_of_length_le hlen,List.drop_eq_nil_of_le hlen]


/-- A nonconstant finite binary word has an adjacent opposite pair. -/
theorem adjacent_or_uniform {V : Type} (χ : V → Bool) (x : V) (xs : List V) :
    (∃ pre a b post, x::xs = pre ++ a::b::post ∧ χ a ≠ χ b) ∨
    (∀ z ∈ x::xs, χ z = χ x) := by
  induction xs generalizing x with
  | nil => exact Or.inr (by simp)
  | cons y ys ih =>
    by_cases hxy : χ x = χ y
    · rcases ih y with h | h
      · obtain ⟨pre,a,b,post,he,hab⟩ := h
        exact Or.inl ⟨x::pre,a,b,post,by simp only [List.cons_append,he],hab⟩
      · exact Or.inr (by
          intro z hz
          rcases List.mem_cons.mp hz with hz | hz
          · subst z; rfl
          · exact (h z hz).trans hxy.symm)
    · exact Or.inl ⟨[],x,y,ys,rfl,hxy⟩

/-- Balance counts true and false endpoints, not just list-length parity. -/
def Balanced {V : Type} (χ : V → Bool) (xs : List V) : Prop :=
  xs.countP χ = xs.countP (fun x => !χ x)

theorem balanced_adjacent {V : Type} (χ : V → Bool) (x : V) (xs : List V)
    (hb : Balanced χ (x::xs)) :
    ∃ pre a b post, x::xs = pre ++ a::b::post ∧ χ a ≠ χ b := by
  rcases adjacent_or_uniform χ x xs with h | hu
  · exact h
  · exfalso
    have ht : (x::xs).countP χ = if χ x then (x::xs).length else 0 := by
      cases hx : χ x
      · simp only [Bool.false_eq_true,↓reduceIte]
        apply List.countP_eq_zero.mpr
        intro z hz
        simp [hu z hz,hx]
      · simp only [↓reduceIte]
        apply List.countP_eq_length.mpr
        intro z hz
        simp [hu z hz,hx]
    have hf : (x::xs).countP (fun z => !χ z) = if χ x then 0 else (x::xs).length := by
      cases hx : χ x
      · simp only [Bool.false_eq_true,↓reduceIte]
        apply List.countP_eq_length.mpr
        intro z hz
        simp [hu z hz,hx]
      · simp only [↓reduceIte]
        apply List.countP_eq_zero.mpr
        intro z hz
        simp [hu z hz,hx]
    unfold Balanced at hb
    cases hx : χ x <;> simp only [hx, Bool.false_eq_true, ↓reduceIte, List.length_cons] at ht hf
    all_goals omega


/-- Removing opposite adjacent endpoints preserves exact balance. -/
theorem balanced_remove_pair {V : Type} (χ : V → Bool)
    (pre post : List V) (a b : V) (hab : χ a ≠ χ b)
    (h : Balanced χ (pre ++ a::b::post)) : Balanced χ (pre ++ post) := by
  unfold Balanced at *
  simp only [List.countP_append,List.countP_cons] at *
  cases ha : χ a <;> cases hb : χ b <;> simp only [ha,hb] at hab h
  all_goals simp_all <;> omega

/-- Every balanced finite binary endpoint word admits an actual noncrossing
opposite-side matching, with exactly the original endpoint order. -/
theorem exists_forest {V : Type} (χ : V → Bool) (xs : List V)
    (hb : Balanced χ xs) : ∃ F : Forest V χ, F.flatten = xs := by
  cases xs with
  | nil => exact ⟨.empty,rfl⟩
  | cons x xs =>
    obtain ⟨pre,a,b,post,he,hab⟩ := balanced_adjacent χ x xs hb
    have hrest : Balanced χ (pre ++ post) :=
      balanced_remove_pair χ pre post a b hab (he ▸ hb)
    have hshort : (pre ++ post).length < (x::xs).length := by
      have hlen := congrArg List.length he
      simp only [List.length_append,List.length_cons] at hlen ⊢
      omega
    obtain ⟨F,hF⟩ := exists_forest χ (pre ++ post) hrest
    obtain ⟨G,hG⟩ := F.insert_pair a b hab pre.length
    refine ⟨G,?_⟩
    rw [hF,List.take_append_length,List.drop_append_length] at hG
    simp only [List.append_assoc,List.cons_append,List.nil_append] at hG
    exact hG.trans he.symm
termination_by xs.length
decreasing_by
  simp_wf
  simp_all only [List.length_append,List.length_cons]


def Forest.pairCount {V : Type} {χ : V → Bool} : Forest V χ → Nat
  | .empty => 0
  | .concat u v => u.pairCount + v.pairCount
  | .bracket _ u _ _ => u.pairCount + 1

theorem Forest.flatten_length {V : Type} {χ : V → Bool} (F : Forest V χ) :
    F.flatten.length = 2*F.pairCount := by
  induction F with
  | empty => rfl
  | concat u v ihu ihv => simp only [flatten,pairCount,List.length_append,ihu,ihv]; omega
  | bracket x u y h ihu =>
    simp only [flatten,pairCount,List.length_cons,List.length_append,List.length_nil,ihu]
    omega

/-- The grammar does not conceal an assumed pairing: it implies balance. -/
theorem Forest.balanced {V : Type} {χ : V → Bool} (F : Forest V χ) :
    Balanced χ F.flatten := by
  induction F with
  | empty => rfl
  | concat u v ihu ihv =>
    unfold Balanced at *
    simp only [flatten,List.countP_append,ihu,ihv]
  | bracket x u y h ihu =>
    unfold Balanced at *
    simp only [flatten,List.countP_append,List.countP_cons,List.countP_nil]
    cases hx : χ x <;> cases hy : χ y <;> simp_all <;> omega

theorem exists_forest_iff {V : Type} (χ : V → Bool) (xs : List V) :
    (∃ F : Forest V χ, F.flatten=xs) ↔ Balanced χ xs := by
  constructor
  · rintro ⟨F,rfl⟩; exact F.balanced
  · exact exists_forest χ xs

/-- Distinct occurrences, including repeated endpoint values, are matched by
actual list positions. The flattened position word is exactly 0,1,...,n−1. -/
theorem exists_position_forest {V : Type} (χ : V → Bool) (xs : List V)
    (hb : Balanced χ xs) :
    ∃ F : Forest (Fin xs.length) (fun i => χ xs[i]),
      F.flatten=List.finRange xs.length := by
  have hm : (List.finRange xs.length).map (fun i => xs[i])=xs := by
    simp [List.finRange,List.map_ofFn,Function.comp_def]
  have hi : Balanced (fun i : Fin xs.length => χ xs[i]) (List.finRange xs.length) := by
    unfold Balanced at hb ⊢
    rw [←hm] at hb
    simpa only [List.countP_map,Function.comp_def] using hb
  exact exists_forest _ _ hi

#print axioms exists_forest
#print axioms exists_position_forest

end ErdePaths.NoncrossingMatch
