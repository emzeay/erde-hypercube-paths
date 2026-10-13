import ErdePaths.Conjecture

/- Supplementary optimization arithmetic, included in the default library build.
The ordinary graph-counting identities connecting cardinality to these parameters
are proved in Part II of proof-ai-generated.md, not assumed as axioms here. -/
namespace ErdePaths.Consequences.Optimization

def edges (n : Nat) : Nat := n*2^(n-1)
def frontier (n d : Nat) : Nat := d*2^(n-d.log2-1)
def Admissible (n L : Nat) : Prop := 1≤L ∧ L<2^n ∧ L∣edges n

private theorem pow_gt (n : Nat) : n<2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; have := Nat.two_pow_pos n; omega

private theorem edges_half {n : Nat} (hn : 2≤n) (heven : n%2=0) :
    edges n=(n/2)*2^n := by
  have hne : n=(n-1)+1 := by omega
  have hp : 2^n=2^(n-1)*2 := by
    calc
      2^n=2^((n-1)+1) := congrArg (fun x => 2^x) hne
      _=2^(n-1)*2 := Nat.pow_succ _ _
  have hn2 : n/2*2=n := by omega
  unfold edges
  rw [hp,Nat.mul_comm (2^(n-1)) 2,←Nat.mul_assoc,hn2]

/-- The edge-count capacity lower bound, valid for variable path lengths too. -/
theorem capacity_lower_bound {n K : Nat} (hn : 2≤n) (heven : n%2=0)
    (hcapacity : edges n≤K*(2^n-1)) : n/2+1≤K := by
  have hpow := Nat.two_pow_pos n
  have he := edges_half hn heven
  by_cases h : n/2+1≤K
  · exact h
  · have hk : K≤n/2 := by omega
    have hm := Nat.mul_le_mul_right (2^n-1) hk
    have hb := Nat.le_trans hcapacity hm
    rw [Nat.mul_sub_left_distrib,Nat.mul_one,←he] at hb
    have hr : 0<n/2 := by omega
    have hx : n/2≤edges n := by
      rw [he]
      have hh := Nat.mul_le_mul_left (n/2) (show 1≤2^n by omega)
      simpa using hh
    omega

/-- Every odd-divisor frontier is actually attained by the proved construction. -/
theorem frontier_exists {n d : Nat} (hn : 2≤n) (heven : n%2=0)
    (hd : 0<d) (ho : d%2=1) (hdiv : d∣n) :
    HasPathDecomposition n (frontier n d) := by
  obtain ⟨m,hm,he⟩ := Parameters.dimension_multiplier hn heven hd ho hdiv
  unfold frontier
  rw [he]
  exact OddFrontiers.frontiers m d hm hd ho

theorem frontier_admissible {n d : Nat} (hn : 2≤n) (_heven : n%2=0)
    (hd : 0<d) (hdiv : d∣n) : Admissible n (frontier n d) := by
  have hdn : d≤n := Nat.le_of_dvd (by omega) hdiv
  have hr : d.log2<n := by
    apply (Nat.log2_lt (by omega : d≠0)).mpr
    exact Nat.lt_of_le_of_lt hdn (pow_gt n)
  have hx : n-d.log2-1+(d.log2+1)=n := by omega
  have hpow := Nat.two_pow_pos (n-d.log2-1)
  refine ⟨by unfold frontier; exact Nat.succ_le_of_lt (Nat.mul_pos hd hpow),?_,?_⟩
  · unfold frontier
    have hh := Nat.mul_lt_mul_of_pos_right (Nat.lt_log2_self (n:=d)) hpow
    rw [Nat.mul_comm (2^(d.log2+1)), ←Nat.pow_add,hx] at hh
    exact hh
  · have he : edges n=n*2^(n-d.log2-1)*2^d.log2 := by
      unfold edges
      rw [Nat.mul_assoc,←Nat.pow_add]
      congr 2
      omega
    rw [he]
    unfold frontier
    exact Nat.dvd_mul_right_of_dvd (Nat.mul_dvd_mul_right hdiv _) _

/-- Exact frontier path-count arithmetic. Graph counting gives E/L paths. -/
theorem frontier_count {n d : Nat} (hn : 2≤n) (hd : 0<d) (hdiv : d∣n) :
    edges n/frontier n d=(n*2^d.log2)/d := by
  have hdn : d≤n := Nat.le_of_dvd (by omega) hdiv
  have hr : d.log2<n := (Nat.log2_lt (by omega : d≠0)).mpr
    (Nat.lt_of_le_of_lt hdn (pow_gt n))
  have he : edges n=(n*2^d.log2)*2^(n-d.log2-1) := by
    unfold edges
    rw [Nat.mul_assoc,←Nat.pow_add]
    congr 2
    omega
  rw [he]
  exact Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _)

/-- Each admissible length is dominated by an attained odd-divisor frontier.
Together with frontier_count this verifies the finite-minimum formula. -/
theorem optimizer_reduction {n L : Nat} (hn : 2≤n) (heven : n%2=0)
    (hL : Admissible n L) :
    ∃ d, 0<d ∧ d%2=1 ∧ d∣n ∧ Admissible n (frontier n d) ∧
      HasPathDecomposition n (frontier n d) ∧
      (n*2^d.log2)/d≤edges n/L := by
  obtain ⟨d,b,hd,ho,hb⟩ := Parameters.odd_part L (by have := hL.1; omega)
  have hdn := Parameters.odd_divisor_dimension ho hb hL.2.2
  have hLf := Parameters.frontier_divides hd hb hL.2.1
  have hf := frontier_admissible hn heven hd hdn
  refine ⟨d,hd,ho,hdn,hf,frontier_exists hn heven hd ho hdn,?_⟩
  rw [←frontier_count hn hd hdn]
  exact Nat.div_le_div_left (Nat.le_of_dvd (by have := hf.1; omega) hLf)
    (by have := hL.1; omega)

/-- A divisor of a power of two is itself a power of two. -/
private theorem divisor_power_two {k n : Nat} (hk : 0<k) (hdiv : k∣2^n) :
    ∃ s, k=2^s := by
  obtain ⟨d,s,hd,ho,he⟩ := Parameters.odd_part k hk
  have hdk : d∣k := he ▸ Nat.dvd_mul_right d (2^s)
  have hdp := Nat.dvd_trans hdk hdiv
  have hd1 : d∣1 := (Profile.odd_coprime_power_two ho n).dvd_of_dvd_mul_left
    (by simpa using hdp)
  have hdone : d=1 := by have := Nat.le_of_dvd (by decide : 0<1) hd1; omega
  exact ⟨s,by simpa [hdone] using he⟩

/-- Necessity: an equal-length partition reaching the capacity bound must
have a Mersenne half-dimension. The count identity is supplied explicitly. -/
theorem optimal_dimension_necessary {n L : Nat} (hn : 2≤n) (heven : n%2=0)
    (hcount : edges n=(n/2+1)*L) :
    ∃ s, 1≤s ∧ n=2*(2^s-1) := by
  let k := n/2+1
  have hdiv : k∣edges n := ⟨L,hcount⟩
  have he : edges n=(k-1)*2^n := by
    have hk : k-1=n/2 := by simp [k]
    rw [hk]
    exact edges_half hn heven
  have hh : k∣k*2^n-edges n := Nat.dvd_sub (Nat.dvd_mul_right k (2^n)) hdiv
  have hsub : k*2^n-edges n=2^n := by
    rw [he]
    have hk : k=(k-1)+1 := by simp [k]
    have hmul : k*2^n=(k-1)*2^n+2^n := by
      calc
        k*2^n=((k-1)+1)*2^n := congrArg (fun x => x*2^n) hk
        _=(k-1)*2^n+2^n := by rw [Nat.add_mul,Nat.one_mul]
    exact (congrArg (fun x => x-(k-1)*2^n) hmul).trans
      (Nat.add_sub_cancel_left _ _)
  rw [hsub] at hh
  obtain ⟨s,hs⟩ := divisor_power_two (by dsimp [k]; omega) hh
  refine ⟨s,?_,?_⟩
  · by_cases h : 1≤s
    · exact h
    · have hz : s=0 := by omega
      simp [hz,k] at hs
      omega
  · dsimp [k] at hs
    omega

/-- Sufficiency, with an actual Lean path decomposition and its count arithmetic. -/
theorem optimal_family (s : Nat) (hs : 1≤s) :
    let n := 2*(2^s-1)
    ∃ L, Admissible n L ∧ HasPathDecomposition n L ∧
      edges n=(n/2+1)*L := by
  let n := 2*(2^s-1)
  have hp : s<2^s := pow_gt s
  have hn : 2≤n := by dsimp [n]; omega
  have heven : n%2=0 := by dsimp [n]; omega
  have hsn : s≤n := by dsimp [n]; omega
  let L := (2^s-1)*2^(n-s)
  have hpow : 2^n=2^s*2^(n-s) := by rw [←Nat.pow_add,Nat.add_sub_of_le hsn]
  have hE : edges n=(2^s-1)*2^n := by
    have hn' : n/2=2^s-1 := by dsimp [n]; omega
    rw [edges_half hn heven,hn']
  have hcount : edges n=(n/2+1)*L := by
    have hk : n/2+1=2^s := by dsimp [n]; omega
    rw [hk,hE,hpow]
    dsimp [L]
    rw [←Nat.mul_assoc,Nat.mul_comm (2^s-1) (2^s),Nat.mul_assoc]
  have ha : Admissible n L := by
    refine ⟨?_,?_,⟨n/2+1,hcount.trans (Nat.mul_comm _ _)⟩⟩
    · dsimp [L]
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (Nat.two_pow_pos _))
    · rw [hpow]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
  exact ⟨L,ha,Conjecture.paths n L hn heven ha.1 ha.2.1 ha.2.2,hcount⟩


/-- Local degree bookkeeping in a capacity-optimal path partition:
internal, endpoint and omitted path occurrences give only these two cases. -/
theorem vertex_deficit {k n internal endpoint omitted : Nat} (hk : 2≤k)
    (hn : n=2*(k-1)) (hpaths : internal+endpoint+omitted=k)
    (hdegree : endpoint+2*internal=n) :
    (endpoint=2 ∧ omitted=0) ∨ (endpoint=0 ∧ omitted=1) := by
  omega

/-- A simple path in the numbered cube cannot exceed the vertex capacity. -/
theorem simple_path_capacity {n L : Nat} {p : List (Vertex n)}
    (hp : IsSimplePath L p) : L<2^n := by
  have hsub : p⊆List.finRange (2^n) := by intro x _; exact List.mem_finRange x
  have hl := hp.2.1.length_le_of_subset hsub
  rw [List.length_finRange,hp.1] at hl
  omega


/-- A finite simple-path family cannot cover more edges than its vertex
capacity permits. The encoding can forget edge orientation. -/
theorem finite_family_capacity {V : Nat} {E : Type}
    (ps : List (List (Fin V))) (es : List E) (encode : Fin V × Fin V → E)
    (hpaths : ∀ p∈ps, p.Nodup) (hedges : es.Nodup)
    (hcover : es⊆ps.flatMap (fun p => (steps p).map encode)) :
    es.length≤ps.length*(V-1) := by
  have hl := hedges.length_le_of_subset hcover
  have hb : (ps.flatMap (fun p => (steps p).map encode)).length≤ps.length*(V-1) := by
    clear hcover hl
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hp := hpaths p (by simp)
      have hsub : p⊆List.finRange V := by intro x _; exact List.mem_finRange x
      have hc := hp.length_le_of_subset hsub
      rw [List.length_finRange] at hc
      have hi := ih (fun p hp => hpaths p (by simp [hp]))
      have hs : (steps p).length=p.length-1 := by
        simp [steps,List.length_zip,List.length_tail]
      simp only [List.flatMap_cons,List.length_append,List.length_map,hs,List.length_cons]
      rw [Nat.add_mul,Nat.one_mul]
      omega
  exact Nat.le_trans hl hb

#print axioms finite_family_capacity
#print axioms vertex_deficit
#print axioms simple_path_capacity
#print axioms capacity_lower_bound
#print axioms optimizer_reduction
#print axioms optimal_dimension_necessary
#print axioms optimal_family
end ErdePaths.Consequences.Optimization
