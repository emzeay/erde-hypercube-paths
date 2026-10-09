import ErdePaths.SourceLocalLengths
import ErdePaths.SourceRoom
import ErdePaths.EvenHamilton

namespace ErdePaths.SourceUniformInput
open SourceLocalFold SourceClock SourceProfile HamiltonTower

/-- One explicit profile handles arbitrary source depth and subdivision.
The A=2 branch is the singleton zero; higher powers use the uniform interval. -/
def selector {N : Nat} (r : Nat) : Fin N→Bool :=
  Profile.intervalWithEndpoint (if r=1 then 0 else 2^(r-1))

theorem selector_odd {N r : Nat} (hr : 1≤r) (room : 2^r<N) :
    Profile.cardinality (selector (N:=N) r)%2=1 := by
  by_cases he : r=1
  · simp only [selector,he,↓reduceIte]
    exact Profile.intervalWithEndpoint_odd (by have := Nat.two_pow_pos r; omega) (by decide)
  · have hpow : 2*2^(r-1)=2^r := by rw [Nat.mul_comm,←Nat.pow_succ]; congr 1; omega
    have hev : 2^(r-1)%2=0 := by
      have hp : r-1=(r-2)+1 := by omega
      rw [hp,Nat.pow_succ]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)
    simp only [selector,he,↓reduceIte]
    exact Profile.intervalWithEndpoint_odd (by omega) hev

theorem selector_prefix {N r : Nat} (hr : 1≤r) (room : 2^r<N) :
    Profile.prefixCount (selector (N:=N) r) (2*2^(r-1))=2^(r-1) := by
  by_cases he : r=1
  · subst r
    simp only [selector,↓reduceIte,Nat.sub_self,Nat.pow_zero]
    rw [Profile.intervalWithEndpoint_prefix 0 2 (by omega)]
    decide
  · simp only [selector,he,↓reduceIte]
    apply Profile.intervalWithEndpoint_balanced_prefix
    have hp : 2*2^(r-1)=2^r := by rw [Nat.mul_comm,←Nat.pow_succ]; congr 1; omega
    omega

/-- Genuine cube inputs for every ordinary higher-weight parameter. All
Hamilton factors and source profiles are constructed here. -/
noncomputable def input (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 1≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) : Input := by
  have he : 2≤2*m := by omega
  have hsum : R-2+1+1=R := by omega
  have hroom : R≤2*m*2^(R-2) := SourceRoom.prefix_room hm hR
  have hpr : 2^r<2^(2*m*2^(R-2)) :=
    (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr (by omega)
  have hf : m*(2*2^(R-2+1-r))=m*2^(R-r) := by
    rw [Nat.mul_comm 2,←Nat.pow_succ]
    congr 2
    omega
  refine {
    e:=2*m, d:=2*(m*2^(R-r)), m:=m, u:=2^(r-1)
    B:=2^(2*(m*2^(R-r))), b:=b, a:=R-2, h:=1, r:=r
    hB:=Nat.two_pow_pos _, he:=he, hr:=by omega, hh:=by decide
    room:=?_, hA:=?_
    D:=EvenHamilton.decomposition m (by omega)
    S:=fun _ _=>selector r
    ho:=fun _ _=>selector_odd hr hpr
    balance:=fun _ _=>selector_prefix hr hpr
    HD:=?_, last:=⟨0,Nat.two_pow_pos _⟩
    z:=⟨if r=1 then 1 else 2,?_⟩, hz:=?_
    hB4:=?_, evenB:=?_, short:=by simpa only [hsum] using hb, odd:=ho }
  · rw [lengthPower_pow,hsum]
    exact Nat.pow_dvd_pow 2 hroom
  · rw [Nat.mul_comm,←Nat.pow_succ]; congr 1; omega
  · exact EvenHamilton.castData rfl hf.symm rfl
      (EvenHamilton.decomposition (m*2^(R-r)) (Nat.mul_pos (by omega) (Nat.two_pow_pos _)))
  · split
    · have : 2^r=2 := by rw [‹r=1›]
      omega
    · have hp : 2≤r := by omega
      have : 4≤2^r := Nat.pow_le_pow_right (by decide : 1≤2) hp
      omega
  · dsimp only
    split <;> decide
  · have hm' : 1≤m*2^(R-r) := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
    exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega : 2≤2*(m*2^(R-r)))
  · have hp : 2*(m*2^(R-r))=(2*(m*2^(R-r))-1)+1 := by
      have := Nat.mul_pos (by omega : 0<m) (Nat.two_pow_pos (R-r)); omega
    rw [hp,Nat.pow_succ]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left 2 _)

/-- The actual palette graph is the J cube of the required dimension,
with its genuine even-cube Hamilton factors and exact paired half-length. -/
noncomputable def jData (m b : Nat) (hm : 1≤m) (ho : b%2=1) :
    HamiltonData.DecompositionData (Vertex (2*m*b)) (@Adjacent (2*m*b))
      (m*b) (2*2^(2*m*b-1)) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) := by
  have hb : 0<b := by omega
  have hp : 0<m*b := Nat.mul_pos (by omega) hb
  have hl : 2^(2*(m*b))=2*2^(2*m*b-1) := by
    have he : 2*(m*b)=(2*m*b-1)+1 := by rw [Nat.mul_assoc]; omega
    rw [he,Nat.pow_succ,Nat.mul_comm]
  exact EvenHamilton.castData (by ac_rfl) rfl hl (EvenHamilton.decomposition (m*b) hp)

theorem j_half_ge_two (m b : Nat) (hm : 1≤m) (ho : b%2=1) :
    2≤2^(2*m*b-1) := by
  have hb : 1≤b := by omega
  have hp : 1≤m*b := Nat.mul_le_mul hm hb
  have he : 2*m*b=2*(m*b) := Nat.mul_assoc _ _ _
  exact Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤2*m*b-1 by rw [he]; omega)

/-- The literal coordinate blocks have the target dimension. -/
theorem dimension (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 1≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1) :
    let I := input m R r b hm hR hr hrR hb ho
    I.e*2^(I.a+I.h+1)+I.d+2*m*b=2*m*(2^R+2^(R-r)+b) := by
  change 2*m*2^(R-2+1+1)+2*(m*2^(R-r))+2*m*b=_
  rw [show R-2+1+1=R by omega,Nat.mul_add,Nat.mul_add]
  ac_rfl

/-- Derived actual length at these dimensions, uniform in arbitrary R,r,b. -/
theorem length (m R r b : Nat) (hm : 1≤m) (hR : 3≤R)
    (hr : 1≤r) (hrR : r<R) (hb : b<2^(R-r)) (ho : b%2=1)
    (n : (input m R r b hm hR hr hrR hb ho).Index) :
    let I := input m R r b hm hR hr hrR hb ho
    I.length (jR:=2^(2*m*b-1)) n=
      (2^R+2^(R-r)+b)*2^(2*m*(2^R+2^(R-r)+b)-R-1) := by
  let I := input m R r b hm hR hr hrR hb ho
  have hp : 1≤2*m*b := by
    have hb : 1≤b := by omega
    have hp := Nat.mul_le_mul hm hb
    rw [Nat.mul_assoc]
    omega
  have hh := SourceLocalLengths.frontier_length I n (2*(m*2^(R-r))) (2*m*b) hp rfl
  change I.length (jR:=2^(2*m*b-1)) n=_
  change I.length (jR:=2^(2*m*b-1)) n=
    (2^(R-2+1+1)+2^(R-2+1+1-r)+b)*
    2^((2*m)*2^(R-2+1+1)+2*(m*2^(R-r))+2*m*b-(R-2+1+1)-1) at hh
  have he := dimension m R r b hm hR hr hrR hb ho
  change 2*m*2^(R-2+1+1)+2*(m*2^(R-r))+2*m*b=_ at he
  rw [he,show R-2+1+1=R by omega] at hh
  exact hh

#print axioms input
#print axioms jData
#print axioms dimension
#print axioms length
end ErdePaths.SourceUniformInput
