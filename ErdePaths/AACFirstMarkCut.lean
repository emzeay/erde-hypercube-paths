import ErdePaths.AACFineCoarseBridge
import ErdePaths.SourceMarkSize

namespace ErdePaths.AACFirstMarkCut
open SquareLift AACIntervalSplit AACMarkIntervals

def indices {E : Nat} (S : Fin E→Bool) : List (Fin E) := (List.finRange E).filter S

theorem mem_indices {E : Nat} (S : Fin E→Bool) (i : Fin E) : i∈indices S ↔ S i=true := by
  simp only [indices,List.mem_filter,List.mem_finRange,true_and]

private theorem count_list (f : Nat→Bool) (n : Nat) :
    TurnPatterns.count f n=(List.ofFn (fun i : Fin n=>f i.val)).countP id := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [TurnPatterns.count,List.ofFn_succ_last,List.countP_append]
    change TurnPatterns.count f n+(f n).toNat=
      (List.ofFn (fun i : Fin n=>f i.val)).countP id+([f n]).countP id
    rw [ih]
    cases f n <;> simp

theorem indices_length {E : Nat} (S : Fin E→Bool) : (indices S).length=Profile.cardinality S := by
  let f : Nat→Bool := fun n=>if hn : n<E then S ⟨n,hn⟩ else false
  have hf : (fun i : Fin E=>f i.val)=S := by funext i; simp only [f,dite_eq_left i.isLt,Fin.eta]
  have hp := TurnPatterns.prefix_numeric (N:=E) f E (Nat.le_refl _)
  rw [hf,count_list] at hp
  have he : (List.ofFn (fun i : Fin E=>f i.val))=(List.finRange E).map S := by
    rw [List.finRange,List.map_ofFn]
    exact congrArg List.ofFn hf
  rw [he,List.countP_map] at hp
  unfold indices Profile.cardinality
  rw [←List.countP_eq_length_filter]
  simpa only [Function.comp_def,id_eq] using hp.symm

/-- Prefix ordinals enumerate the same literal sorted mark list. -/
theorem indices_markIndex {E : Nat} (S : Fin E→Bool) :
    indices S=(List.finRange (Profile.cardinality S)).map (markIndex S) := by
  have hi : Function.Injective (markIndex S) := by
    intro j k he
    have hj := (markIndex_spec S j).2
    have hk := (markIndex_spec S k).2
    rw [he] at hj
    exact Fin.ext (by omega)
  have hn : ((List.finRange (Profile.cardinality S)).map (markIndex S)).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange _).imp (fun hne he=>hne (hi he))
  have hp : (indices S).Perm ((List.finRange (Profile.cardinality S)).map (markIndex S)) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange E).filter S) hn).mpr
    intro i
    change i∈indices S ↔ i∈(List.finRange (Profile.cardinality S)).map (markIndex S)
    rw [mem_indices]
    constructor
    · intro hs
      have hstep : Profile.prefixCount S (i.val+1)=Profile.prefixCount S i.val+1 := by
        simp only [Profile.prefixCount,Profile.indicator,dite_eq_left i.isLt,hs,Bool.toNat_true]
      have hm := prefix_mono S (show i.val+1≤E by have := i.isLt; omega)
      let j : Fin (Profile.cardinality S) := ⟨Profile.prefixCount S i.val,by
        change Profile.prefixCount S i.val<Profile.prefixCount S E
        omega⟩
      have he : markIndex S j=i := marked_level_unique S _ _ (markIndex_spec S j).1 hs
        ((markIndex_spec S j).2.trans (show j.val+1=Profile.prefixCount S (i.val+1) from hstep.symm))
      exact List.mem_map.mpr ⟨j,List.mem_finRange _,he⟩
    · rintro hm
      obtain ⟨j,_,hj⟩ := List.mem_map.mp hm
      exact hj ▸ (markIndex_spec S j).1
  have hs : (indices S).Pairwise (fun a b=>a.val≤b.val) := (List.pairwise_le_finRange E).filter S
  have ht : ((List.finRange (Profile.cardinality S)).map (markIndex S)).Pairwise (fun a b=>a.val≤b.val) := by
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange _).imp (fun hlt=>Nat.le_of_lt (markIndex_order S _ _ hlt))
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba=>Fin.ext (Nat.le_antisymm hab hba)) hs ht hp

noncomputable def cut {E : Nat} (S : Fin E→Bool) (hq : 0<Profile.cardinality S) : Fin E :=
  markIndex S ⟨0,hq⟩

theorem cut_mark {E : Nat} (S : Fin E→Bool) (hq : 0<Profile.cardinality S) : S (cut S hq)=true :=
  (markIndex_spec S ⟨0,hq⟩).1

theorem cut_le_mark {E : Nat} (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (i : Fin E) (hi : S i=true) : (cut S hq).val≤i.val := by
  have hc := marked_level_before S ⟨0,hq⟩
  have hstep : Profile.prefixCount S (i.val+1)=Profile.prefixCount S i.val+1 := by
    simp only [Profile.prefixCount,Profile.indicator,dite_eq_left i.isLt,hi,Bool.toNat_true]
  by_cases hh : (cut S hq).val≤i.val
  · exact hh
  · have hm := prefix_mono S (show i.val+1≤(cut S hq).val by omega)
    change Profile.prefixCount S (cut S hq).val=0 at hc
    omega

def flags {E : Nat} (hE : 0<E) (S : Fin E→Bool) (c : Fin E) (n : Fin E) : Bool := S (forward hE c n)

theorem cut_zero {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    flags hE S (cut S hq) ⟨0,hE⟩=true := by
  rw [flags,forward_zero]
  exact cut_mark S hq

/-- No retained mark wraps into the interval before the first original mark. -/
theorem no_wrap {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (n : Fin E) (hn : flags hE S (cut S hq) n=true) :
    (cut S hq).val+n.val<E := by
  have hc := (cut S hq).isLt
  have hni := n.isLt
  have hmin := cut_le_mark S hq (forward hE (cut S hq) n) hn
  change (cut S hq).val≤((cut S hq).val+n.val)%E at hmin
  by_cases hlt : (cut S hq).val+n.val<E
  · exact hlt
  · rw [Nat.mod_eq_sub_mod (by omega)] at hmin
    rw [Nat.mod_eq_of_lt (by omega : (cut S hq).val+n.val-E<E)] at hmin
    omega

/-- Rotating at the first mark preserves the EXACT ordered mark indices,
not merely their set or their multiplicities. -/
theorem indices_rotate {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    (indices (flags hE S (cut S hq))).map (forward hE (cut S hq))=indices S := by
  let T := flags hE S (cut S hq)
  have hn : ((indices T).map (forward hE (cut S hq))).Nodup := by
    apply List.pairwise_map.mpr
    exact ((List.nodup_finRange E).filter T).imp
      (fun hne he=>hne (forward_injective hE (cut S hq) he))
  have hp : ((indices T).map (forward hE (cut S hq))).Perm (indices S) := by
    apply (List.perm_ext_iff_of_nodup hn ((List.nodup_finRange E).filter S)).mpr
    intro i
    constructor
    · intro hi
      obtain ⟨n,hn,he⟩ := List.mem_map.mp hi
      exact (mem_indices S i).mpr (he ▸ (mem_indices T n).mp hn)
    · intro hi
      let n := backward hE i (cut S hq)
      have he : forward hE (cut S hq) n=i := forward_inverse hE _ _
      refine List.mem_map.mpr ⟨n,(mem_indices T n).mpr ?_,he⟩
      change S (forward hE (cut S hq) n)=true
      rw [he]
      exact (mem_indices S i).mp hi
  have hs : (indices S).Pairwise (fun a b=>a.val≤b.val) :=
    (List.pairwise_le_finRange E).filter S
  have ht : ((indices T).map (forward hE (cut S hq))).Pairwise (fun a b=>a.val≤b.val) := by
    apply List.pairwise_map.mpr
    apply ((List.pairwise_le_finRange E).filter T).imp_of_mem
    intro i j hi hj hij
    have hwi := no_wrap hE S hq i ((mem_indices T i).mp hi)
    have hwj := no_wrap hE S hq j ((mem_indices T j).mp hj)
    change ((cut S hq).val+i.val)%E≤((cut S hq).val+j.val)%E
    rw [Nat.mod_eq_of_lt hwi,Nat.mod_eq_of_lt hwj]
    exact Nat.add_le_add_left hij _
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba=>Fin.ext (Nat.le_antisymm hab hba)) ht hs hp

theorem cardinality_rotate {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hq : 0<Profile.cardinality S) :
    Profile.cardinality (flags hE S (cut S hq))=Profile.cardinality S := by
  have hh := congrArg List.length (indices_rotate hE S hq)
  simpa only [List.length_map,indices_length] using hh

private theorem finRange_cast {N M : Nat} (he : N=M) :
    (List.finRange N).map (Fin.cast he)=List.finRange M := by
  cases he
  simp

/-- Exact ordinal lookup after the first-mark cut; the old descriptor
word can be used at each actual new mark without any reordering premise. -/
theorem markIndex_rotate {E : Nat} (hE : 0<E) (S : Fin E→Bool) (hq : 0<Profile.cardinality S)
    (j : Fin (Profile.cardinality S)) :
    forward hE (cut S hq)
      (markIndex (flags hE S (cut S hq)) (Fin.cast (cardinality_rotate hE S hq).symm j))=markIndex S j := by
  let T := flags hE S (cut S hq)
  have hc := cardinality_rotate hE S hq
  have hcast : (List.finRange (Profile.cardinality S)).map (Fin.cast hc.symm)=List.finRange (Profile.cardinality T) := finRange_cast hc.symm
  have hw := indices_rotate hE S hq
  rw [indices_markIndex,indices_markIndex,←hcast,List.map_map] at hw
  have hv := congrArg (fun ls : List (Fin E)=>ls[j.val]?) hw
  simp only [List.finRange,List.map_ofFn,List.getElem?_ofFn,j.isLt,↓reduceDIte] at hv
  exact Option.some.inj hv

/-- Physical mark words retain original chronological order after this cut. -/
theorem word_rotate {E : Nat} {V : Type} (hE : 0<E) (S : Fin E→Bool)
    (hq : 0<Profile.cardinality S) (base : Fin E→V) :
    (indices (flags hE S (cut S hq))).map (fun n=>base (forward hE (cut S hq) n))=
      (indices S).map base := by
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map base) (indices_rotate hE S hq)

theorem cyclicFlag_rotate {E : Nat} (hE : 0<E) (color : Fin E→Bool) (c : Fin E) :
    cyclicFlag hE (fun n=>color (forward hE c n))=flags hE (cyclicFlag hE color) c := by
  funext n
  simp only [cyclicFlag,flags,AACIntervalSplit.forward_predecessor]

#print axioms indices_rotate
#print axioms word_rotate
#print axioms cardinality_rotate
end ErdePaths.AACFirstMarkCut
