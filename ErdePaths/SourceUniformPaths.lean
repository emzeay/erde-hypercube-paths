import ErdePaths.SourceGlobalPaths
import ErdePaths.SourceUniformInput
import ErdePaths.GraphTarget
import ErdePaths.OddClassification

namespace ErdePaths.SourceUniformPaths

private theorem input_reserved (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 2≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    2≤(SourceUniformInput.input m R r b hm hR (by omega) hrR hb ho).r := hr

private theorem input_origin (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 2≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    (SourceUniformInput.input m R r b hm hR (by omega) hrR hb ho).z.val=2 := by
  change (if r=1 then 1 else 2)=2
  rw [ite_eq_right (by omega)]

private theorem transport {n N L K : Nat} (hn : n=N) (hL : L=K)
    (D : GraphPathDecomposition (Vertex n) (@Adjacent n) L) :
    HasPathDecomposition N K := by
  subst N
  subst K
  exact GraphTarget.to_target D

/-- Genuine simple-path decomposition of the ordinary buffered frontier.
All Hamilton factors, profiles, schedules, forks and global edge ownership
are constructed internally; only numerical parameter restrictions remain. -/
theorem decomposition (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 2≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    HasPathDecomposition (2*m*(2^R+2^(R-r)+b))
      ((2^R+2^(R-r)+b)*2^(2*m*(2^R+2^(R-r)+b)-R-1)) := by
  let I := SourceUniformInput.input m R r b hm hR (by omega) hrR hb ho
  let t := 2^(2*m*b-1)
  have ht : 0<t := Nat.two_pow_pos _
  have h2 : 2≤t := SourceUniformInput.j_half_ge_two m b hm ho
  have hn : 0<I.m*2^(I.a+I.h+1) := by
    change 0<m*2^(R-2+1+1)
    exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  let n : I.Index := ⟨0,hn⟩
  have hl := SourceUniformInput.length m R r b hm hR (by omega) hrR hb ho n
  have hl' := SourceGlobalFold.Input.length_eq I ht n
  have he : SourceGlobalFold.Input.totalLength I t=
      (2^R+2^(R-r)+b)*2^(2*m*(2^R+2^(R-r)+b)-R-1) := hl'.symm.trans hl
  exact transport (SourceUniformInput.dimension m R r b hm hR (by omega) hrR hb ho) he
    (SourceGlobalPaths.Input.cube I (input_reserved m R r b hm hR hr hrR hb ho)
      (input_origin m R r b hm hR hr hrR hb ho) ht h2
      (SourceUniformInput.jData m b hm ho))

/-- The same actual path theorem in canonical odd-frontier notation. -/
theorem frontier (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 2≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    let d := 2^R+2^(R-r)+b
    HasPathDecomposition (2*m*d) (d*2^(2*m*d-d.log2-1)) := by
  dsimp only
  rw [OddClassification.coefficient_log2 (show R-r<R by omega) hb]
  exact decomposition m R r b hm hR hr hrR hb ho

#print axioms decomposition
#print axioms frontier
end ErdePaths.SourceUniformPaths
