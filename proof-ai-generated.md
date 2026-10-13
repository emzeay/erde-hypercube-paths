# AI-generated proof and consequences

This document gives the construction proving Erde’s even-hypercube path-decomposition conjecture, its consequences, and a map to the Lean sources. The conjecture appeared in [*Decomposing the cube into paths*](https://doi.org/10.1016/j.disc.2014.07.019), published in 2014 after a 2013 preprint. This is a provisional research exposition. External independent mathematical review has not been completed.

For every even integer n≥2 and integer ℓ≥1 with ℓ<2^n and ℓ dividing n·2^(n−1), the edges of the binary cube Q_n partition into simple paths of exactly ℓ edges. Paths may share vertices. A simple path has no repeated vertex. Edges are undirected.

All graphs are finite and simple. A path’s length is its number of edges. Write V(G) and E(G) for the vertex and edge sets of G. The cube Q_n has 2^n vertices and n·2^(n−1) edges. A Cartesian product edge changes exactly one coordinate along an edge of its factor graph.

Lean’s kernel checks the formal declarations. The final verification section distinguishes the fully formalized core theorem and graph-transfer existence statements from supplementary counting arguments that remain prose.

- [Part I: Proof](#part-i-proof-of-the-even-hypercube-path-decomposition-statement)
- [Part II: Consequences](#part-ii-consequences-of-the-even-hypercube-path-decomposition-theorem)

## Part I: Proof of the even-hypercube path-decomposition statement

### Construction conventions

The formal proof is complete source code in `ErdePaths/`, concluding in [Conjecture.lean](ErdePaths/Conjecture.lean). The exposition below explains its uniform construction. Detailed local statements and their proofs are in the linked Lean modules. No external research notes or experimental certificates are needed to check the theorem. The formal proof map at the end of Part I relates the argument to those modules.

An even-dimensional cube Q_(2m) has a Hamiltonian decomposition into m cycles, each of length 2^(2m). This is an established result, discussed by [Alspach, Bermond, and Sotteau](https://doi.org/10.1007/978-94-009-0517-7_2). The formalization proves it internally in [EvenHamilton.lean](ErdePaths/EvenHamilton.lean).

A vertex’s **cyclic position** is its index in a chosen traversal of a cycle. A **representing set** consists of vertices selected at equally spaced cyclic positions. We call these vertices **representatives**. The representing sets and anchored products used below follow [Axenovich, Offner, and Tompkins](https://doi.org/10.1016/j.ejc.2021.103320). A **profile** chooses the positive direction followed at each height of a square torus. An **alternating anchored circuit (AAC)** is the transition construction on an anchored product described in §4. Its **marks** are the unique internal vertices where its interval color changes. Binary **source addresses** record square-factor choices. All coordinates and congruences below refer to actual cyclic position functions, so the construction must establish physical edge ownership as well as numerical counts.

Natural-number exponents and remainders in the Lean files have their ordinary integer meaning under the bounds proved alongside each use. The exponent r of the highest binary bit used below is called R in the numerical frontier interfaces. Their parameter r is the exponent of A.

### 1. Reduction to one maximal length for each odd divisor

Write ℓ=d·2^a with d odd. Divisibility implies d divides n, since d is coprime to 2^(n−1). As n is even, n=2md for an integer m≥1. Put r=⌊log₂d⌋. Then

    2^r≤d<2^(r+1),     a≤n−r−1

The second inequality follows from ℓ<2^n. The exponent n−r−1 is nonnegative because d≤n and n≥2 imply r≤n−1. Set

    M_d=d·2^(n−r−1)

This length is strictly less than 2^n, divides n·2^(n−1) with quotient 2m·2^r, and is divisible by ℓ. Cut each simple M_d-path into consecutive ℓ-edge segments. Each segment remains simple, and the segments partition the original path’s edges. Thus it suffices to construct paths of length M_d for every odd d and n=2md.

For a fixed odd divisor d, M_d is the longest admissible length with that odd part. Every shorter admissible length with the same odd part divides M_d, so cutting supplies all of them. We repeat the construction separately for each odd divisor of n.

The four families are disjoint and exhaustive. An odd number has a one in its lowest binary position. If that is its only one, it equals 1. If it has two ones, it is a power of two plus one. Otherwise it has at least three ones, and its occupied positions either contain a gap or are all consecutive.

| Family | Form | Construction below |
|---|---|---|
| One | d=1 | Hamiltonian cycles cut in half |
| Two binary ones | d=2^r+1, r≥1 | §3 |
| Higher binary weight, non-Mersenne | At least three ones, with a gap between the highest and lowest bits | §5 |
| Higher binary weight, Mersenne | d=2^(r+1)−1, r≥2 | §6 |

For d=1, cut the Hamiltonian cycles of Q_n into their two equal halves. This gives length 2^(n−1), including the four-cycle Q_2. Subdivision handles every smaller admissible power of two.

### 2. Standard square factors and hierarchical representative decoding

We use the classical square construction of Ringel, as described by [Mollard and Ramras, §4](https://doi.org/10.1007/s00373-013-1402-0). A Hamiltonian cycle of even length N≥4 on X gives coordinates on its square C_N□C_N. This product is a torus, a grid with wraparound in both coordinates. The two square tours have cyclic position formulas

    I₊(i,j)=iN+(i−j mod N)
    I₋(i,j)=(−j mod N)N+(i−j mod N)

They are Hamiltonian cycles and partition the torus edges. If D divides N, both indices reduce to i−j modulo D. All cycle indices here begin at the common physical zero. Repeated squaring of each original factor E_t partitions the edges of the cube of doubled dimension at each stage. Every coordinate edge has a unique parent factor owner, and the two child factors partition its torus. Here a factor is a spanning subgraph. Each factor in this construction is a Hamiltonian cycle.

After j squarings from Q_(2m), the parent cycle length is

    N_j=2^(2m·2^j)

An address records the successive square-tour choices as bits, with choice 0 for the column tour and choice 1 for the row tour. The earliest choice occupies the lowest, rightmost bit. After r squarings, the descendants have all addresses from 0 to 2^r−1.

At step j, the inequality 2m·2^j≥j+1 implies that 2^(j+1) divides N_j. With the earlier choices fixed, the two square-tour position formulas therefore agree modulo 2^(j+1). Later squarings preserve that agreement by taking differences. Thus the final cyclic position at a fixed physical vertex agrees through bit j, independently of the current and later choices.

We can now find the unique factor whose cyclic position equals its address modulo 2^r. Read the position’s lowest bit to select the first tour choice. With that choice fixed, read the next bit to select the second, and continue. At each step, agreement through the next bit makes the choice well-defined before the later choices have been made. The completed address satisfies the required congruence, and every choice was forced. This proves both existence and uniqueness. Section 5 adapts this decoding to the source and profile construction needed for higher binary weight.

### 3. Odd parts with two binary ones

Let d=P+1, P=2^r, r≥1. Apply r standard squarings to each E_t of Q_(2m), producing P Hamiltonian factors of G=Q_(2mP). Assign source branch j to address bit j. The inequality 2m·2^j≥j+1 holds for every j≥0, so the decoding in §2 gives, at every physical G vertex, exactly one factor with actual index congruent to its address modulo P.

Write V(F) for the vertex set of a graph F. These cyclic residue sets partition V(G) within each t-group and have spacing P along their cycles. Pair each such group with E_t on H=Q_(2m), represented by every H vertex. The anchored products have all G-direction cycle edges at every H vertex, and H-direction cycle edges precisely at the selected G representatives. They partition G□H edges by the two unique owners.

Each product is a rectangular torus with first-axis subdivision P, underlying lengths 2^(2mP−r) and 2^(2m), both even and at least 4. The two-wiggle construction, the two-cycle case of [Axenovich, Offner, and Tompkins, §4.1, Proposition 3](https://doi.org/10.1016/j.ejc.2021.103320), gives two simple cycles of equal length. At a representative in row 0, its two nearest first-coordinate interior neighbors belong exclusively to opposite cycles. They are distinct degree-two vertices because P≥2. Apply a fork exchange, as in [Saranya, Jeevadoss, Nalini, and Chitra, Construction 1](https://doi.org/10.1080/09728600.2024.2444564). Remove one incident edge from each cycle and give it to the other. Each cycle opens into a path and gains an edge to a vertex absent from that cycle, preserving simplicity and length. The anchored product has (1+1/P)·2^n edges, so each path has length

    (P+1)·2^(n−r−1)=M_d

There are 2mP paths. The square construction supplies the representatives, the two wiggles supply the cycles, and the fork exchange opens them into the required paths.

### 4. Construction for higher binary weight

Both higher-weight families use the same assembly. We first partition the base edges into anchored products, construct marked Euler circuits on them, and pair and label their marks. The third coordinate block then turns each circuit into two simple cycles. A fork exchange opens those cycles into paths. Sections 5 and 6 supply the required representative groups and marks.

Every remaining odd d has a unique representation

    d=P+L+b,     P=2^r>L=2^s≥2,     1≤b<L odd
    A=P/L

A vertex’s phase modulo D means its cyclic position reduced modulo D.

Use coordinate blocks G=Q_(2mP), H=Q_(2mL), J=Q_(2mb). For each original t, construct P Hamiltonian factors of G arranged into L old groups of A factors. Each old group must have representatives spaced A edges apart along their cycles, with the representative sets partitioning V(G). These old representatives determine where to attach H. The marks introduced below determine where to attach J. Assign the L H Hamiltonian factors in its t-block to these old groups, representing every H vertex. The resulting anchored products partition G□H edges. Their underlying torus has first-axis subdivision A and lengths

    K₀=2^(2mP)/A,     B=2^(2mL)

Write C=|V(G□H)| and T=|V(J)|. Each anchored product contains C larger-block edges and C/A smaller-block edges, so its edge count is E=C+C/A=(P+L)C/P. The patterns below have periods 2L or 4L. Both divide K₀ because 2mP≥r+2, so 2mP−log₂A≥log₂L+2.

A cube vertex’s physical parity is the number of ones in its binary label modulo 2. Every cube edge changes this parity. A set of marks has balanced physical parity when it contains equally many vertices of each parity.

#### Alternating anchored circuits

We use alternating anchored circuits in the sense of the [SUAMI work of Antonio, Loftis, and O’Connor](https://julianaoconnor.com/files/Poster_SUAMI_Group_G.pdf). Here an AAC is an Euler circuit with an even number q≥4 of distinct marks, each visited once. Every unmarked vertex is visited either once or twice. When visited twice, its two appearances lie in intervals of opposite parity when the intervals between successive marks are numbered in Euler order.

On the underlying torus use a balanced periodic binary turn pattern independent of the H row. At each grid vertex the turn pairs each first-coordinate direction with a second-coordinate direction. Second-coordinate edges from row j to row j+1 receive color j modulo 2. A subdivided first-coordinate interval has one internal color change exactly when its neighboring turn bits agree. That internal degree-two vertex is its mark. Unmarked degree-two vertices have a constant color. Each grid vertex has one transition visit of each color.

For any balanced turn pattern, the transition invariant w=σ(−1)^(turn) (σ denotes the H traversal direction) makes the first coordinate advance by a fixed unit and gives zero net H displacement after K₀ macros. Hence there are B baseline unoriented circuits. When turn_(−1)=1 and turn₀=turn₁=0, flipping column 0 in every H row except the last merges consecutive circuit labels in a chain, leaving exactly one Euler circuit. Each flip replaces one interval 0 mark by one interval −1 mark, a displacement A along the G cycle.

Index every H factor so its last vertex is the same physical h*. Suppose two G factors have forward A-edge paths joining the same physical vertices u and v, whose phases are c and c+A in both factors. Reverse the first factor and keep the second forward. Use u as the designated endpoint of the reversed factor and v as that of the forward factor. Their surgeries exchange marks between the same two physical endpoints at every H vertex except h*. Thus paired surgery preserves global pointwise mark multiplicity, even when the factors use different H cycles.

Marks are distinct degree-two vertices and are visited once. Grid vertices occur twice, once in each color, hence in Euler intervals of opposite mark parity. These are the exact hypotheses for simple folded outputs.

#### Noncrossing labels and two cycles

For each initial Hamiltonian index t, the marks below cover each physical G□H vertex exactly b times. Divide the mb Hamiltonian cycles of J into m disjoint groups of b cycles, one for each t. We pair and label marks separately within each t-group. Each individual AAC has balanced physical marked parity. Its G marks have constant parity, its baseline mark count is the same in every H row, and the surgery moves a mark by the even distance A within one row. The H cycle has equal numbers of rows of each physical parity.

A balanced cyclic binary mark word admits a noncrossing perfect matching joining opposite physical parities. Recursively remove adjacent opposite symbols and restore the pairs after matching the remaining word. The resulting chords are nested or disjoint. Within each t-group, their union is a b-regular bipartite multigraph on physical G□H vertices, with no loops. The multigraph edges represent pairs of marks and need not be edges of the base graph.

For a vertex set S on one side, its b|S| incident edges end in its neighbor set N(S), giving b|S|≤b|N(S)|. This is [Hall’s condition](https://doi.org/10.1112/jlms/s1-10.37.26). Remove perfect matchings successively and label them by the b Hamiltonian cycles assigned to t. Every physical base vertex receives each label of its group exactly once. Across all t-groups, it receives all mb labels exactly once.

For each AAC, form cyclic mark layers on X=V(J), with the assigned label's actual Hamiltonian cycle as vertical edges in its layer. Color horizontal edges (j,x)—(j+1,x) by π(x)+j+1 modulo 2, where π is the physical parity on J. Split each vertical label cycle into alternating matchings A_label,B_label. Choose one chord as active. Output 0 takes A at its opening and B at its closing. Passive chords take A at both ends. Output 1 takes the complements.

Every vertex has one horizontal and one vertical edge of each color. Cut before the active opening. Every passive chord lies wholly inside or outside the active chord. Recursively cancel innermost passive pairs, whose two identical matching involutions become adjacent. The return permutations are exactly BA and AB. Each is a single cycle on either bipartition side because A∪B is Hamiltonian. Hence both outputs are Hamiltonian on the abstract layered vertex set. No commuting matchings or common label order are assumed.

Expand horizontal layer edges along their actual AAC intervals. A repeated physical AAC vertex appears in opposite interval parities, so its occurrences enter different outputs at every J coordinate. Marks occur once. Both expanded cycles are therefore simple. Every AAC edge has half its J copies in each output. Every marked layer contributes half its J-cycle edges. Thus their common length is

    |V(J)|(E+q)/2

where q is the AAC's number of marks. Per-label mark ownership partitions every J-direction edge, and the first anchored ownership already partitions all other edges.

The constructions below have q=bC/P. They give length

    |V(J)|(E+q)/2 = (P+L+b)·2^(n−r−1)=M_d

A fork with two exclusive neighbors opens each cycle pair without changing length or ownership. There are mP AACs and 2mP paths.

### 5. The non-Mersenne case

Assume either A≥4 or A=2,b≤L−3. Then r≥3. Choose K=2^k to be the least power of two at least max(1,r/(2m)). For r≥3, the inequality r≤2m·2^(r−2) gives K≤P/4. Thus 2mK≥r and h=r−k−1≥1. Apply k standard squarings to each E_t, obtaining K sources of length R=2^(2mK), divisible by P. Put a=log₂A. The formalization uses the permitted choice K=P/4. The argument below works for either choice.

Assign source branch j to code position j if j<a, and j+1 if j≥a, reserving bit a for a fresh profile twin. Write p(j)=j for j<a and p(j)=j+1 otherwise. Source parent exponents satisfy 2m·2^j≥p(j)+1. Within a source torus, put height=x+y modulo R. The first profile factor advances x when the height belongs to S and advances y otherwise. The second takes the other positive edge. Use S={0} for A=2 and S={0,…,A/2−1}∪{A} otherwise. The number |S| is odd and hence coprime to R. After R steps, the first profile translates each height fiber by (|S|,−|S|), and the second translates it by (−|S|,|S|). Each translation is one cycle on that fiber, so both factors are Hamiltonian. Their first A-edge paths have coordinate words x^(A/2)y^(A/2) and y^(A/2)x^(A/2). Both are simple and join (0,0) to (A/2,A/2). We call the two profile factors twins.

Both profiles have cyclic position x+y modulo P. Apply h=r−k−1≥1 upper standard lifts. Within each source every final factor shares a cyclic position function χ_source modulo P. Source-prefix congruences persist because profiles take sums and upper square tours take differences. Assign the profile bit a and remaining h positions to the paired upper configurations. There are P factors with all r-bit codes once.

The common-path lift prescribes each pair's literal endpoint phases c,c+A. For a required fixed-coordinate phase, each parent path forbids at most one connector candidate. A phase fiber containing three vertices therefore has a choice avoiding both exclusions. The profile parent length R²≥P²≥3P supplies them. Thus arbitrary final codes are genuine geometric endpoints.

For the shifted decoding, fix a physical vertex g and a shift δ modulo P. Read χ_source(g)−δ from its lowest bit upwards. At a source position p(j), the earlier source choices determine that bit independently of the undecided suffix, so it selects exactly one source branch. The reserved profile bit and the upper-choice bits select their corresponding choices. Once the source is fixed, its position function is independent of those profile and upper choices. This gives exactly one final factor. If two shifts agree modulo 2A=2^(a+1), the entire decoding through the profile bit a is identical, so both selected factors have the same profile choice.

For every physical x and every δ modulo P, decoding gives exactly one factor with χ_source(x)=code+δ. Reverse profile bit 0 and retain profile bit 1 forward. Their mark classes are code−Au and code+Au respectively, u=0,…,b−1. The two shift owners for −Au and +Au have the same profile bit, because these shifts agree modulo 2A. Exactly one is eligible. It is the negative-shift owner if that bit is 0 and the positive-shift owner if it is 1. Different u cannot duplicate one factor's mark. This proves exactly b marks per physical G vertex.

Use the balanced anti-L pattern

    turn_i=0 for 0≤i≤b
    turn_i=(i−b) mod 2 for b<i<L
    turn_(i+L)=1−turn_i

Its agreement starts are 0,…,b−1 modulo L. The first seam has 1,0,0 as required. The common-pair flips preserve b-fold coverage.

Choose mark offset z=2 for A≥4 and z=1 for A=2. After choosing the orientation, index each factor so that its designated physical endpoint has local cyclic position z. The old representatives are the vertices at local positions 0 modulo A. In the unreversed cyclic position function, their phase classes are code+z for reversed factors and code−z for forward factors modulo A. Reversal changes the sign of the displacement from the designated endpoint, which explains the two signs. Fix all high code bits, including the profile bit, and vary all low a bits. Restricted decoding gives one old representative owner at each x. These are L groups of A factors, including source branches among the low bits.

For A≥4 each mark's neighbors at offsets 1 and 3 are unique unmarked degree-two vertices in opposite interval colors. This supplies the fork at the mark. For A=2,b≤L−3, turn_(b+1) is isolated in the common unflipped row h*. Both adjacent intervals are unmarked, so the two nearest internal degree-two neighbors give the fork at that grid vertex. The assembly in §4 yields the target paths in all these cases, including r=3, d=11 and d=13.

### 6. The Mersenne case

The remaining case is A=2, b=L−1, d=2P−1. For r≥4, choose K=2^k to be the larger of 4 and the least power of two at least (r+2)/(2m). Then 4≤K≤P/4 and r+2≤2mK. The upper bound follows from r+2≤2m·2^(r−2). The K source cycles have length R divisible by D=4P. The formalization again uses the permitted maximal source depth K=P/4. In either choice h=r−k−1≥1. A=2 profiles followed by h upper lifts give P factors. Literal endpoint phases c,c+2 can be prescribed modulo D by the same connector avoidance.

Use the balanced period 2P turn word

    0^(P−1) 1^4 0 1^(P−4)

Its disagreement starts are B₀={P−2,P+2,P+3,2P−1}. In a reverse profile twin, unmarked offsets relative to its own code are −2B₀. In the forward twin they are +2B₀.

There are r free code positions in 0,…,r+1. Bits 2 and 3 are fixed zero. Code bit 0 is source branch β₀, bit 1 is the profile twin ε, and bit 4 is β₁ when m≥2 and β₁(1−β₀) when m=1. Source branch j≥2 occupies bit j+3. Upper configurations occupy the remaining high positions. A pair has codes c,c+2 without carry. Numerical codes can repeat across distinct sources in the exceptional m=1 branch with β₀=1. Their physical cyclic positions will distinguish them.

Every source cyclic position function has common physical parity. Within fixed β₀ all suffix cyclic position functions agree modulo 16. At branch j≥2 cyclic position functions agree through bit j+3 because 2m·2^j≥j+4. At branch 1 they agree modulo 32 when m≥2. When m=1, the two siblings obtained by varying β₁ satisfy χ₁=17χ₀ modulo 32, a difference of 16 times physical parity. Subsequent profile sums and upper square-tour differences preserve these identities.

Fix a physical G vertex. Its cyclic position parity uniquely chooses β₀. The eight combinations of ε and its four disagreement offsets, including the code's +2ε, exhaust all even residues modulo 16 exactly once. The common cyclic position modulo 16 therefore chooses exactly one ε and one full offset δ modulo D. Subtract this full δ before further decoding, retaining every carry.

For β₀=0 or m≥2, ordinary bit 4 decoding chooses β₁. For m=1 and β₀=1, both code bit 4 values are zero, but the two cyclic position functions differ by 16, so exactly one has the required bit 4 after subtraction. Later source bits are uniquely selected by their common-prefix cyclic positions. The remaining upper bits complete χ−δ. Thus exactly one factor is unmarked at every physical G vertex.

Old spacing-two groups fix all construction choices except β₀ and pair its two choices. Codes have opposite parity, so their old representatives partition V(G), independently of the exceptional bit 4 change. There are L groups. Each physical vertex lies in the interior of a subdivided segment in L products. Removing the unique unmarked appearance leaves L−1 marks. Reciprocal profile-pair flips preserve this coverage. The turn word's isolated zero at P+3 in the unflipped h* row gives the exclusive-neighbor fork. The assembly yields length (2P−1)·2^(n−r−1).

#### The boundary d=15

For r=3, d=15, perform two standard squarings on each starting Hamiltonian factor of Q_(2m). This gives four source cycles on Q_(8m). Label the column-tour descendants at the first squaring as sources 0 and 1, and the row-tour descendants as sources 2 and 3. Within each pair, use the lower source number for the column tour at the second squaring and the higher number for the row tour. Thus each pair shares its first branch and differs in its second. These are source names, not the binary addresses used earlier. Their modulo 32 sibling correction is the same scalar 17 when m=1. The phase starts are 0,16,1,1 when m=1 and 0,16,1,17 when m≥2. They partition the unmarked classes, including the corrected sibling relation. There are zero upper lifts, so use explicit shifted single-height profiles S={c}. The common two-edge paths (0,c)→(1,c+1) have phases c,c+2. This supplies genuine endpoints without assuming arbitrary phase prescription. Use the long turn word with P=8. Relative to a pair’s start c, its unmarked classes are

    U={20,12,10,2,14,22,24,0} modulo 32

The sets U and U+16 partition the even residues modulo 32. Multiplication by 17 fixes even residues, so sources 0 and 1 cover every even-parity vertex exactly once. For odd residues, sources 2 and 3 give U+1 and U+17. When m=1, source 3 expresses its set as U+1, but its sibling position function differs by 16 on odd vertices, converting it to U+17 in source 2’s coordinates. Thus there is exactly one unmarked appearance at every physical vertex.

The two profiles in sources 0 and 1 have odd old representatives, and those in sources 2 and 3 have even old representatives. Pair across these pools to obtain four old groups. Every physical vertex then has four interior appearances and one unmarked appearance, leaving three marks. The shared endpoints make the switches reciprocal. Balanced marked parity, the long pattern, and the common last row supply the labeling and fork conditions of §4.

#### The boundary d=7

For r=2, d=7, square each E_t once to obtain two source cycles with common cyclic position function modulo 4. On their squares use positive profiles S={0} and S={1}. Their literal two-step endpoints have phases 0,2 and 1,3. All four profile cycles share the same cyclic position function given by a sum modulo 4. Reverse the first owner of each pair and keep its partner forward. Source 0 old representatives have odd physical parity. Source 1 old representatives have even physical parity. Cross-source pairing supplies two old groups for H=Q_(4m). The four mark classes partition G=Q_(8m). Use turn 0011 and the common h* merge chain. Reciprocal endpoint exchanges preserve the mark partition. In any flipped row, column 1 has neighboring turns 1,0,1, so both incident vertical intervals are unmarked and give exclusive A=2 interior neighbors. Fold with E_t on J=Q_(2m) and open the fork, giving 8m paths of length 7·2^(14m−3). This explicit shifted-profile boundary needs no arbitrary zero-lift phase prescription.

For r=1, d=3, the two-binary-ones construction in §3 applies.

### 7. Proof of the full statement

Odd part d=1 is covered by cutting Hamiltonian cycles. Every two-bit odd part is P+1 and is covered by §3. Every odd part with at least three ones is uniquely P+L+b. Non-Mersenne cases fall in §5, including their minimal r=3 boundary. Mersenne cases fall in §6, including d=7 and d=15. No admissible odd divisor is omitted. Each maximal length M_d therefore has a simple path decomposition, and §1 cuts it into the requested ℓ-edge paths.

`OddFrontiers.frontiers` implements this exhaustive branch assembly. `Conjecture.erde_even_hypercube` applies `Parameters.target_from_odd_frontiers` to the actual proved frontiers. `Conjecture.paths` exposes the exact quantified hypotheses and the simple-path edge-partition conclusion. The theorem has no surviving factor, mark-count, schedule, geometry, frontier-existence or coverage hypothesis.

### Formal proof map

All paths below are relative to this repository. Importing [Conjecture.lean](ErdePaths/Conjecture.lean) imports the complete dependency closure. The mathematical construction is uniform in m and in the binary complexity of the positive odd remainder b.

| Part of the argument | Lean sources and public entry points |
|---|---|
| Exact graph and path statement | [Basic](ErdePaths/Basic.lean): `Adjacent`, `IsSimplePath`, `HasPathDecomposition`; [Binary](ErdePaths/Binary.lean): binary-tuple bijection and adjacency; [GraphTarget](ErdePaths/GraphTarget.lean): `GraphTarget.to_target` |
| Arithmetic reduction and subdivision (§1) | [Parameters](ErdePaths/Parameters.lean): `normalize`, `frontier_divides`, `target_from_odd_frontiers`; [Subdivision](ErdePaths/Subdivision.lean): `subdivision` |
| Actual even-cube Hamiltonian factors | [EvenHamilton](ErdePaths/EvenHamilton.lean): `decomposition`; [HamiltonSquare](ErdePaths/HamiltonSquare.lean), [HamiltonTower](ErdePaths/HamiltonTower.lean) |
| Actual square cyclic positions and causal ownership (§2) | [SquareLift](ErdePaths/SquareLift.lean), [HierarchicalDecode](ErdePaths/HierarchicalDecode.lean), [SourceProfile](ErdePaths/SourceProfile.lean), [SourceStability](ErdePaths/SourceStability.lean), [SourceAnchorGroups](ErdePaths/SourceAnchorGroups.lean) |
| Two-bit frontiers (§3) | [TwoBitFrontier](ErdePaths/TwoBitFrontier.lean): `frontier`; [AnchoredAssembly](ErdePaths/AnchoredAssembly.lean), [SubdividedWiggle](ErdePaths/SubdividedWiggle.lean), [ForkWiggle](ErdePaths/ForkWiggle.lean) |
| Actual AAC traversal and marks (§4) | [AACTransition](ErdePaths/AACTransition.lean), [AACMerge](ErdePaths/AACMerge.lean), [AACFineClock](ErdePaths/AACFineClock.lean), [AACMarkWord](ErdePaths/AACMarkWord.lean), [AACPatternCardinality](ErdePaths/AACPatternCardinality.lean) |
| Reciprocal endpoint exchange (§4) | [ReciprocalEndpoints](ErdePaths/ReciprocalEndpoints.lean), [AACMarkExchange](ErdePaths/AACMarkExchange.lean), [SourceMarkMulticover](ErdePaths/SourceMarkMulticover.lean) |
| Balanced marks, Hall labels and noncrossing return (§4) | [AACPhysicalBalance](ErdePaths/AACPhysicalBalance.lean), [NoncrossingMatch](ErdePaths/NoncrossingMatch.lean), [HallMarriage](ErdePaths/HallMarriage.lean), [HallColor](ErdePaths/HallColor.lean), [MarkSchedule](ErdePaths/MarkSchedule.lean), [LayerPartition](ErdePaths/LayerPartition.lean) |
| Simple folded tours and exact local/global edge ownership (§4) | [AACFoldClock](ErdePaths/AACFoldClock.lean), [AACFoldEdgeLedger](ErdePaths/AACFoldEdgeLedger.lean), [SourceLocalFold](ErdePaths/SourceLocalFold.lean), [SourceMarkedProduct](ErdePaths/SourceMarkedProduct.lean), [CubePairedPartition](ErdePaths/CubePairedPartition.lean) |
| Ordinary buffered frontiers (§5) | [SourceUniformInput](ErdePaths/SourceUniformInput.lean): `input`; [SourceGlobalPaths](ErdePaths/SourceGlobalPaths.lean): `Input.cube`; [SourceUniformPaths](ErdePaths/SourceUniformPaths.lean): `frontier` |
| Ordinary isolated frontiers (§5) | [AACIsolatedOpening](ErdePaths/AACIsolatedOpening.lean), [SourceIsolatedPaths](ErdePaths/SourceIsolatedPaths.lean), [SourceIsolatedFrontier](ErdePaths/SourceIsolatedFrontier.lean): `frontier` |
| Complementary frontiers (§6) | [MersenneCodeOrigins](ErdePaths/MersenneCodeOrigins.lean), [MersenneReciprocalMulticover](ErdePaths/MersenneReciprocalMulticover.lean), [MersenneUniformInput](ErdePaths/MersenneUniformInput.lean), [MersenneUniformPaths](ErdePaths/MersenneUniformPaths.lean): `frontier` |
| Forced zero-depth boundaries (§6) | [ZeroUpperCodeOrigins](ErdePaths/ZeroUpperCodeOrigins.lean), [ZeroUpperIncidence](ErdePaths/ZeroUpperIncidence.lean), [QuarterProfileOrigins](ErdePaths/QuarterProfileOrigins.lean), [QuarterReciprocalMulticover](ErdePaths/QuarterReciprocalMulticover.lean), [SevenFrontier](ErdePaths/SevenFrontier.lean): `frontier`; [FifteenFrontier](ErdePaths/FifteenFrontier.lean): `frontier` |
| Every odd coefficient and the full theorem (§7) | [PowerFrontier](ErdePaths/PowerFrontier.lean), [OddClassification](ErdePaths/OddClassification.lean), [OddFrontiers](ErdePaths/OddFrontiers.lean): `frontiers`; [Conjecture](ErdePaths/Conjecture.lean): `erde_even_hypercube`, `paths` |

The public frontier theorems construct genuine factors, profiles, marks, schedules, local openings and full cube edge ownership internally. The conditional arithmetic theorem `target_from_odd_frontiers` is supplied with the unconditional proved `OddFrontiers.frontiers`. Its premise does not survive in the final theorem.

### Literature for the main proof

These are the sources used in the main proof exposition. Published versions are linked where available. The original preprint identifies the conjecture as Conjecture 8 in §3.

- Joshua Erde, [*Decomposing the cube into paths*](https://doi.org/10.1016/j.disc.2014.07.019), Discrete Mathematics **336** (2014), 41–45. [Original 2013 preprint](https://arxiv.org/abs/1310.6776v1).
- Brian Alspach, Jean-Claude Bermond, and Dominique Sotteau, [*Decomposition into cycles I: Hamilton decompositions*](https://doi.org/10.1007/978-94-009-0517-7_2), in *Cycles and Rays* (1990), 9–18. This supplies the established even-cube Hamiltonian decomposition context.
- Maria Axenovich, David Offner, and Casey Tompkins, [*Long path and cycle decompositions of even hypercubes*](https://doi.org/10.1016/j.ejc.2021.103320), European Journal of Combinatorics **95** (2021), article 103320. Representing sets and anchored products appear in §3, and subdivided wiggles in §4.1, Proposition 3. [Open-access preprint](https://arxiv.org/abs/1905.10114v3).
- Michel Mollard and Mark Ramras, [*Edge decompositions of hypercubes by paths and by cycles*](https://doi.org/10.1007/s00373-013-1402-0), Graphs and Combinatorics **31** (2015), 729–741. Section 4 describes Ringel’s square construction. [Open-access preprint](https://arxiv.org/abs/1205.4161v3).
- D. Saranya, S. Jeevadoss, V. Nalini, and V. Chitra, [*Decomposition of hypercube graphs into paths and cycles having k edges*](https://doi.org/10.1080/09728600.2024.2444564), AKCE International Journal of Graphs and Combinatorics (2025). Construction 1 gives the edge exchange used to open cycle pairs.
- Josue Antonio, Hunter Loftis, and Juli O’Connor, [*Cycle and Path Decompositions of Even Hypercubes*](https://julianaoconnor.com/files/Poster_SUAMI_Group_G.pdf), SUAMI research poster, Carnegie Mellon University (2021), advisor David Offner. This motivates the alternating anchored circuit construction.
- Philip Hall, [*On representatives of subsets*](https://doi.org/10.1112/jlms/s1-10.37.26), Journal of the London Mathematical Society **10** (1935), 26–30. The matching argument labels the paired marks.

The Lean formalization proves the needed inputs internally. These references attribute the established constructions and provide context.

---

## Part II: Consequences of the even-hypercube path-decomposition theorem

The results in this part use the theorem established in [Part I](#part-i-proof-of-the-even-hypercube-path-decomposition-statement). They determine optimal equal-length path counts, describe vertices of certain optimal decompositions, and transfer the theorem to other Cartesian products.

The optimization results concern equal-length decompositions unless unequal lengths are explicitly allowed. The transfer results guarantee lengths inherited from a cube; a full classification in the larger graphs would require further arguments.

### 1. Minimum equal-length path count

For even n≥2, let p_eq(Q_n) be the smallest number of paths in an edge decomposition whose paths all have the same positive length. Then

    p_eq(Q_n) = min { n·2^(⌊log₂d⌋)/d : d is a positive odd divisor of n }

To prove this, a decomposition into ℓ-edge paths must have exactly n·2^(n−1)/ℓ paths. The main theorem shows that the attainable lengths are precisely the positive divisors of n·2^(n−1) below 2^n.

For each positive odd divisor d of n, put r=⌊log₂d⌋. The largest admissible length with this odd part is

    M_d=d·2^(n−r−1)

As established in [Part I, §1](#1-reduction-to-one-maximal-length-for-each-odd-divisor), every admissible length with odd part d divides M_d. Its path count is therefore at least

    n·2^(n−1)/M_d = n·2^r/d

Each M_d is attained by the main theorem. Taking the minimum over the positive odd divisors of n proves the formula.

#### Attaining the edge-count bound

Every decomposition of Q_n into simple paths, with lengths allowed to differ, uses at least n/2+1 paths. An equal-length decomposition attains this bound exactly in the dimensions

    n=2(2^s−1),     s≥1

In these dimensions there are 2^s paths, each of length

    ℓ=(2^s−1)·2^(n−s)

These decompositions are optimal even when unequal path lengths are permitted.

For the lower bound, each path has at most 2^n−1 edges. The number of paths is therefore at least

    ⌈n·2^(n−1)/(2^n−1)⌉ = n/2+1

Indeed, n·2^(n−1)=(n/2)(2^n−1)+n/2, with 0<n/2<2^n−1.

Now suppose an equal-length decomposition has k=n/2+1 paths. Its edge count gives kℓ=(k−1)2^n, so k divides (k−1)2^n. Since k also divides k2^n, subtraction shows that k divides 2^n. Every positive divisor of a power of two is a power of two, so k=2^s for some s≥1. Rearranging gives n=2(2^s−1).

Conversely, in this dimension s≤n and ℓ=(2^s−1)2^(n−s) is positive, below 2^n, and divides the cube’s edge count. The main theorem provides the decomposition, and its number of paths is 2^s=n/2+1.

The first such dimensions are 2, 6, 14, 30, and 62. In the other even dimensions, the minimum formula still determines the exact optimum for equal-length paths. The minimum for paths of unequal lengths remains a separate question.

### 2. Omitted vertex sets

Suppose n≥2 is even and Q_n decomposes into k=n/2+1 positive-length simple paths. Exactly k vertices lie on every path and are endpoints of two paths. Every other vertex is omitted by exactly one path and is never an endpoint.

If the paths have equal length, their omitted sets partition the remaining vertices into k blocks, each of size

    2^n/k−1

For the proof, fix a vertex v. Let i_v count paths on which v is internal, e_v count paths on which it is an endpoint, and a_v count paths on which it is absent. Each path contributes exactly one of these possibilities, giving

    i_v+e_v+a_v=k

An internal appearance uses two incident edges, and an endpoint appearance uses one. Since every incident cube edge is covered once,

    2i_v+e_v=n

Use n=2(k−1) to eliminate i_v. This gives

    e_v+2a_v=2

There are only two nonnegative integer possibilities. Either e_v=2 and a_v=0, or e_v=0 and a_v=1. In the first case, v lies on every path and is an endpoint of two. In the second, it is absent from exactly one path and internal to every other path.

There are 2k endpoint occurrences in total because each positive-length path has two endpoints. Each vertex of the first kind contributes two occurrences, so there are exactly k such vertices. Assign every remaining vertex to the unique path that omits it. This produces the asserted partition.

For equal-length paths, the edge count gives ℓ=(k−1)2^n/k. Each path visits ℓ+1 vertices and therefore omits 2^n−(ℓ+1)=2^n/k−1 vertices. Thus all omitted blocks have the same size.

### 3. Transfer to Cartesian products

A **perfect matching** is a set of edges in which every vertex belongs to exactly one edge. A **perfect-matching factorization** partitions a graph’s edges into perfect matchings.

Let t≥2 be even. Suppose G_1,…,G_t each have a perfect-matching factorization with the same number a of matchings. Then their Cartesian product has a simple ℓ-edge path decomposition for every positive ℓ satisfying

    ℓ<2^t,     ℓ divides t·2^(t−1)

The factor graphs may have different vertex counts. The shared number of matchings is what allows their edges to be grouped into cube components.

If a=0, every factor is edgeless. The product is edgeless, and the empty path family is a decomposition. Suppose a≥1 and number the matchings of G_i as M_(i,1),…,M_(i,a).

For a fixed color c, keep the product edges whose changed coordinate uses its cth matching. Choose one matching edge in each factor. Allowing either endpoint in each coordinate gives 2^t product vertices. Within the color subgraph, changing one endpoint choice traverses precisely one retained edge. These vertices and edges form a copy of Q_t.

For each fixed color, the components are exactly these cubes. Every vertex belongs to a unique matching edge in each coordinate, so it belongs to exactly one component of that color. Every product edge belongs to exactly one color because its changed factor edge has a unique matching owner. Thus the color subgraphs partition the product’s edges.

Apply the main theorem to each cube component. The coordinate embeddings are injective and preserve adjacency, so the transferred paths retain their length and simplicity. Within each component the paths partition its edges. Across all colors and components, they partition every product edge exactly once.

### 4. Graph families and path-count consequences

The transfer applies to the following families for every even t≥2.

| Product family | Perfect matchings per factor |
|---|---|
| Hamming graph H(t,q)=K_q□⋯□K_q, with even q≥2 | q−1 |
| C_(2m₁)□⋯□C_(2m_t), with each m_i≥2 | 2 |
| Products of finite simple a-regular bipartite graphs | a |

Here an a-regular graph has exactly a incident edges at every vertex. A bipartite graph has two vertex parts, with every edge joining different parts.

For K_q, label one vertex ∞ and the others by the residues modulo q−1. For each residue c, pair ∞ with c and pair c+j with c−j for 1≤j≤q/2−1. These pairs form a perfect matching. Because q−1 is odd, every edge between finite residues has a unique midpoint c, and an edge incident with ∞ belongs to the matching indexed by its other endpoint. The q−1 matchings therefore partition E(K_q).

An even cycle has two alternating perfect matchings, obtained by taking every other edge in either of its two possible ways.

For an a-regular bipartite graph with a≥1, count the edges incident with a set S on one side. They all end in its neighbor set N(S), so a|S|≤a|N(S)|. The two sides have equal size by counting all edges. [Hall’s theorem](https://doi.org/10.1112/jlms/s1-10.37.26) therefore supplies a perfect matching covering both sides. Remove it and repeat on the remaining regular bipartite graph. This gives a perfect-matching factorization. The case a=0 is edgeless.

For example, H(6,4) and every product of six even cycles of length at least four admit 48-edge path decompositions. The inherited cube conditions hold because 48<2^6 and 48 divides 6·2^5.

#### Gallai’s path-count bound

Let N=∏|V(G_i)| be the number of product vertices. If the common factor degree is a, the product degree is at. Its edge count and the number of transferred paths are

    |E(G_1□⋯□G_t)|=atN/2
    number of paths=atN/(2ℓ)

Whenever ℓ≥at, this is at most N/2. Gallai’s conjecture asks whether every connected N-vertex graph decomposes into at most ⌈N/2⌉ paths, as discussed by [Gunasekara and Devillers, §1](https://doi.org/10.1007/s10623-024-01493-9). For connected products satisfying these hypotheses, the transferred decompositions meet that bound.

In particular, a product of six even cycles has degree 12. Its 48-edge decomposition uses N/8 paths.

#### Path instances of tree-decomposition conjectures

The Graham–Häggkvist conjecture asks whether every m-regular bipartite graph decomposes into copies of each fixed m-edge tree. Häggkvist’s general-graph conjecture asks for the same conclusion in every 2m-regular graph. These conjectures are described by [Jao, Kostochka, and West, §1](https://doi.org/10.4310/JOC.2013.v4.n4.a6).

Suppose a=2^s with s≥0 and ta<2^t. This implies s≤t−1, so ta divides t2^(t−1). The transfer gives the following path instances.

- A product of t a-regular bipartite factors decomposes into ta-edge paths. The path length equals the product degree, giving an instance of the bipartite conjecture.
- A product of t 2a-regular bipartite factors also decomposes into ta-edge paths. The path length equals half the product degree, giving an instance of the general-graph conjecture.

For example, six 8-regular bipartite factors give 48-edge paths in a 48-regular product. Six 16-regular bipartite factors give 48-edge paths in a 96-regular product. These deductions establish the prescribed decompositions for these product graphs when the fixed tree is a path. Arbitrary regular graphs and arbitrary trees require further results.

Gunasekara and Devillers also study **transitive path decompositions**, in which a group of graph automorphisms preserves the decomposition and acts transitively on its paths. The matching transfer above imposes no symmetry condition or uniform endpoint count. Additional arguments would be needed to establish those properties.

### Formal verification scope

The core theorem in [Conjecture.lean](ErdePaths/Conjecture.lean) supplies the existence input used throughout this document. The consequence Lean modules are included in the default build. The scope below describes their mathematical coverage separately from the core theorem.

The general product transfer and its specializations to even-alphabet Hamming graphs, even-cycle products, and regular bipartite factors are fully formalized in [ProductTransfer.lean](ErdePaths/Consequences/ProductTransfer.lean), including simple paths and unique undirected edge ownership. [Optimization.lean](ErdePaths/Consequences/Optimization.lean) verifies frontier existence, count arithmetic, path capacity, the optimal-dimension arithmetic, and the local endpoint/omission alternatives.

The optimization subsection is not yet an end-to-end Lean theorem. Its global counting arguments, the minimum over all equal-length decompositions, and the global omitted-block counts are proved in prose above. The product path counts and comparisons with Gallai’s bound are also counting deductions in prose. These supplementary formalization boundaries leave the complete core theorem unchanged.

The graph-transfer declarations use namespace `ErdePaths.Consequences.ProductTransfer`; the optimization declarations use `ErdePaths.Consequences.Optimization`.

### Literature for consequences

- Philip Hall, [*On representatives of subsets*](https://doi.org/10.1112/jlms/s1-10.37.26), Journal of the London Mathematical Society **10** (1935), 26–30. The perfect-matching theorem supplies the regular bipartite factorizations.
- Kyle F. Jao, Alexandr V. Kostochka, and Douglas B. West, [*Decomposition of Cartesian products of regular graphs into isomorphic trees*](https://doi.org/10.4310/JOC.2013.v4.n4.a6), Journal of Combinatorics **4** (2013), 469–490. Section 1 describes the tree-decomposition conjectures discussed above.
- Ajani De Vas Gunasekara and Alice Devillers, [*Transitive path decompositions of Cartesian products of complete graphs*](https://doi.org/10.1007/s10623-024-01493-9), Designs, Codes and Cryptography **92** (2024), 4231–4245. Section 1 discusses Gallai’s conjecture and the transitivity requirement.

These references provide attribution and context.
