import ErdePaths.HamiltonLedger
import ErdePaths.HamiltonRows

namespace ErdePaths.HamiltonHost
open HamiltonData HamiltonResidual HamiltonLedger SquareLift

abbrev Host (m N : Nat) := Sum ((Fin m×Fin N)×Fin 4) (Fin N×Fin 4)

def decode {V R m N hN} (d : DecompositionData V R m N hN)
    (C : SourceClock.ClockData V N) : Host m N→(V×Fin 4)×(V×Fin 4)
  | .inl ((f,t),r) => (((d.cycles f).cycle t,r),((d.cycles f).cycle (successor hN t),r))
  | .inr (t,q) => ((C.cycle t,(HamiltonRows.baseZero q).1),
      (C.cycle t,(HamiltonRows.baseZero q).2))

theorem adjacent {V R m N hN} (d : DecompositionData V R m N hN)
    (C : SourceClock.ClockData V N) (a : Host m N) :
    ActualGrid R (decode d C a).1 (decode d C a).2 := by
  cases a with
  | inl a => exact Or.inr ⟨rfl,(d.cycles a.1.1).adjacent a.1.2⟩
  | inr a => exact Or.inl ⟨rfl,HamiltonRows.baseZero_ledger.1 a.2⟩

theorem cover {V R m N hN} (d : DecompositionData V R m N hN)
    (C : SourceClock.ClockData V N) (u v : V×Fin 4) (ha : ActualGrid R u v) :
    ∃a : Host m N, SameEdge (decode d C a) (u,v) := by
  rcases ha with ⟨hb,hr⟩|⟨hr,hb⟩
  · obtain ⟨q,hq⟩ := HamiltonRows.baseZero_ledger.2.1 u.2 v.2 hr
    refine ⟨.inr (C.position u.1,q),?_⟩
    have he := sameEdge_map (fun r => (u.1,r)) hq
    simp only [decode,C.cycle_position]
    have hv : ((u.1,u.2),(u.1,v.2))=(u,v) := Prod.ext rfl (Prod.ext hb rfl)
    exact sameEdge_trans _ _ _ he (Or.inl hv)
  · obtain ⟨f,t,ht⟩ := d.cover u.1 v.1 hb
    refine ⟨.inl ((f,t),u.2),?_⟩
    have he := sameEdge_map (fun x => (x,u.2)) ht
    have hv : ((u.1,u.2),(v.1,u.2))=(u,v) := Prod.ext rfl (Prod.ext rfl hr)
    exact sameEdge_trans _ _ _ he (Or.inl hv)

private theorem horizontal_vertical_ne {V R m N hN} (d : DecompositionData V R m N hN)
    (C : SourceClock.ClockData V N) (a : (Fin m×Fin N)×Fin 4) (b : Fin N×Fin 4) :
    ¬SameEdge (decode d C (.inl a)) (decode d C (.inr b)) := by
  intro he
  have hh := sameEdge_map (fun v : V×Fin 4 => v.1) he
  have hs : (d.cycles a.1.1).cycle a.1.2=(d.cycles a.1.1).cycle (successor hN a.1.2) := by
    rcases hh with hh|hh
    all_goals
      have h0 := congrArg Prod.fst hh
      have h1 := congrArg Prod.snd hh
      exact h0.trans h1.symm
  have ha := (d.cycles a.1.1).adjacent a.1.2
  rw [←hs] at ha
  exact d.loopfree _ ha

/-- Actual host labels are undirected-injective, including mixed-axis edges. -/
theorem unique {V R m N hN} (d : DecompositionData V R m N hN)
    (C : SourceClock.ClockData V N) (a b : Host m N)
    (he : SameEdge (decode d C a) (decode d C b)) : a=b := by
  cases a with
  | inl a => cases b with
    | inl b =>
      have hh := d.unique a.1.1 a.1.2 b.1.1 b.1.2
        (sameEdge_map (fun v : V×Fin 4 => v.1) he)
      have hr : a.2=b.2 := by
        rcases he with he|he
        all_goals exact congrArg (fun p => p.1.2) he
      exact congrArg Sum.inl (Prod.ext (Prod.ext hh.1 hh.2) hr)
    | inr b => exact False.elim (horizontal_vertical_ne d C a b he)
  | inr a => cases b with
    | inl b => exact False.elim (horizontal_vertical_ne d C b a (sameEdge_symm _ _ he))
    | inr b =>
      have ht : a.1=b.1 := by
        have hc : C.cycle a.1=C.cycle b.1 := by
          rcases he with he|he
          all_goals exact congrArg (fun p => p.1.1) he
        have hh := congrArg C.position hc
        simpa only [C.position_cycle] using hh
      have hq := HamiltonRows.baseZero_ledger.2.2 a.2 b.2
        (sameEdge_map (fun v : V×Fin 4 => v.2) he)
      exact congrArg Sum.inr (Prod.ext ht hq)

/-- Explicit full carrier, independent of output-cycle existence. -/
def all (m N : Nat) : List (Host m N) :=
  ((List.finRange m).flatMap fun f => (List.finRange N).flatMap fun t =>
    (List.finRange 4).map fun r => Sum.inl ((f,t),r)) ++
  ((List.finRange N).flatMap fun t => (List.finRange 4).map fun q => Sum.inr (t,q))

theorem mem_all {m N : Nat} (a : Host m N) : a∈all m N := by
  cases a with
  | inl a =>
    rcases a with ⟨⟨f,t⟩,r⟩
    simp [all,List.mem_flatMap,List.mem_map,List.mem_finRange]
  | inr a =>
    rcases a with ⟨t,q⟩
    simp [all,List.mem_flatMap,List.mem_map,List.mem_finRange]

private theorem length_flat_constant {X Y : Type} (l : List X) (f : X→List Y) (n : Nat)
    (hf : ∀x, (f x).length=n) : (l.flatMap f).length=l.length*n := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,hf,ih,Nat.succ_mul,Nat.add_comm]

theorem length_all (m N : Nat) : (all m N).length=4*N*(m+1) := by
  unfold all
  rw [List.length_append]
  have hv : ∀t : Fin N,
      ((List.finRange 4).map fun q => (Sum.inr (t,q) : Host m N)).length=4 := by intro t; simp
  have hh : ∀f : Fin m,
      ((List.finRange N).flatMap fun t => (List.finRange 4).map fun r =>
        (Sum.inl ((f,t),r) : Host m N)).length=N*4 := by
    intro f
    rw [length_flat_constant _ _ 4 (by intro t; simp),List.length_finRange]
  rw [length_flat_constant _ _ (N*4) hh,length_flat_constant _ _ 4 hv,List.length_finRange,List.length_finRange]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_assoc,Nat.mul_comm N 4,Nat.mul_comm m (4*N)]

#print axioms unique
#print axioms cover
#print axioms length_all
end ErdePaths.HamiltonHost
