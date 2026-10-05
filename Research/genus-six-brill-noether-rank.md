# The Brill–Noether rank through genus six

For a finite graph G, the Brill–Noether rank w^r_d(G) is at least k when any r + k prescribed
chips lie in a divisor of degree d and rank at least r. Every connected graph of genus at most six
has the expected Brill–Noether rank:

    w^r_d(G) ≥ min(ρ, d − r)      whenever r ≥ 0 and ρ = ρ(g, r, d) ≥ 0.

The statement is formalized as `GenusSixExistence.bnRankGe_through_six` and
`GenusSixExistence.bnNumber_le_bnRank_through_six` in
[`GenusSixExistence/BrillNoetherRank.lean`](../GenusSixExistence/BrillNoetherRank.lean). This
note gives the proof in prose.

§1 reduces the theorem to three inputs: Brill–Noether existence through genus six; w^1_4 ≥ 1 in
genus five, which follows from the long-handle lemma; and w^1_5 ≥ 2 in genus six, the *triple
witness*. §2 states the triple witness and its descent. §3–§7 prove it by *tripod subtraction*:
attach a tripod at the three prescribed points, count the tropical morphisms of degree five on the
resulting graph of genus eight modulo two, and subtract those that come from morphisms of degree
four on G. §8 says which Lean modules carry which section.

Graphs are finite, connected, loopless multigraphs unless said otherwise. A divisor on a graph is
supported on its vertices, and rank is the rank of Baker and Norine.

## 1. The statement and its reduction

### 1.1 The Brill–Noether rank

Let G have genus g, and let r ≥ 0, d and k ≥ 0 be integers. Say that w^r_d(G) ≥ k if every
effective divisor E of degree r + k is contained in an effective divisor D of degree d and rank at
least r; equivalently, some divisor D of degree d and rank at least r has D − E winnable. The
*Brill–Noether rank* w^r_d(G) is the largest such k, and −1 if G has no divisor of degree d and
rank at least r. This is the discrete form of the Brill–Noether rank of Lim, Payne and Potashnik,
with the normalisation of Len. In Lean it is `Utilities.BNRankGe G r d k` and
`Utilities.bnRank G r d` (`Utilities/Foundations/BrillNoetherRank.lean`).

Two facts frame the statement. First, w^r_d(G) ≥ 0 is Brill–Noether existence: a divisor of rank
at least r contains, up to equivalence, every effective divisor of degree r. Second,
w^r_d(G) ≤ d − r, because E ≤ D; so w^r_d ≥ ρ cannot hold in every degree. On a graph of genus six,
w^1_8 = 7, while ρ(6, 1, 8) = 8.

Here ρ(g, r, d) = g − (r + 1)(g − d + r). Write q = g − d + r, so that ρ = g − (r + 1) q and
d − r = g − q.

### 1.2 Statement

> **Theorem 1.** Let G be a connected finite loopless multigraph of genus g ≤ 6, and let r ≥ 0 and
> d be integers with ρ(g, r, d) ≥ 0. Then
>
>     w^r_d(G) ≥ min(ρ, d − r).
>
> In particular ρ ≤ w^r_d(G) when d ≤ g + r.

The second sentence follows from the first: if q ≥ 0, then ρ = g − (r + 1) q ≤ g − q = d − r.

Lim, Payne and Potashnik prove the metric bound w^r_d(Γ) ≥ min(ρ, g) for every metric graph Γ, by
specialization from algebraic curves. Theorem 1 is about finite graphs and vertex-supported
divisors. Its proof is combinatorial, and it does not compare the discrete and metric ranks.

### 1.3 The elementary cases

* **r = 0.** Then ρ = d, and D = E works.
* **q ≤ 0**, that is, d ≥ g + r. A divisor of degree at least g is winnable, by Riemann–Roch. So
  for every effective D of degree d and every effective F of degree r, D − F is winnable, and D has
  rank at least r. Hence w^r_d = d − r, and d − r ≤ ρ because ρ − (d − r) = −rq ≥ 0.

From here on r ≥ 1 and q ≥ 1, so min(ρ, d − r) = ρ.

* **q = 1**, so d = g − 1 + r and ρ = g − 1 − r. Let E be effective of degree g − 1. Riemann–Roch
  gives r(K − E) = r(E) ≥ 0, so K − E is equivalent to an effective divisor H. Split H = F + B
  with F and B effective, deg F = ρ and deg B = r. Then D = K − F has degree d, Riemann–Roch gives
  r(D) = r(F) + r ≥ r, and D − E ∼ H − F = B ≥ 0.
* **ρ = 0.** Then w^r_d ≥ 0 is existence: through genus five the theorem of Atanasov and
  Ranganathan, formalized in `LowGenus/`, and through genus six
  `GenusSixExistence.brillNoetherExistenceThroughSix`.

### 1.4 The two remaining cases

Suppose r ≥ 1, q ≥ 2 and ρ ≥ 1. Then (r + 1) q < g ≤ 6, which forces r = 1, q = 2 and g ∈ {5, 6}:

| g | r | d | ρ | what is needed |
|---|---|---|---|---|
| 5 | 1 | 4 | 1 | w^1_4 ≥ 1: every effective divisor of degree two lies in an effective divisor of degree four and rank at least one |
| 6 | 1 | 5 | 2 | w^1_5 ≥ 2: every effective divisor of degree three lies in an effective divisor of degree five and rank at least one |

So Theorem 1 follows from existence through genus six and these two statements. Existence alone
gives less: in genus six, a divisor of degree four and rank one plus a chip shows only w^1_5 ≥ 1.

### 1.5 Genus five: pairs from a long handle

Let G have genus five and let x, y be vertices of G.

* *x = y.* Attach a cycle at x. The new graph has genus six, so it carries a divisor of degree four
  and rank at least one, and collapsing the cycle gives one on G that contains 2x
  (`GenusSixExistence.markedRankOneCompletion_diagonal_genus_five`).
* *x ≠ y.* Attach a path of 8|V(G)| + 2 edges from x to y. The new graph is connected of genus six,
  so it carries a divisor of degree four and rank at least one (`GenusSixExistence.criticalPencil`).
  The handle is long, since 2·4·(|V(G)| − 1) < 8|V(G)| + 2, and the long-handle lemma
  (`Utilities.exists_pencil_through_ends_of_handle`, proof in
  [`long-handle-lemma.md`](long-handle-lemma.md)) returns an effective divisor of degree four and
  rank at least one on G with a chip at x and a chip at y.

So w^1_4(G) ≥ 1, with no algebraic input and no subdivision
(`GenusSixExistence.markedRankOneCompletion_genus_five`, `GenusSixExistence.bnRankGe_through_five`,
`GenusSixExistence.bnNumber_le_bnRank_through_five`). §2.4 explains why gadgets alone do not reach
genus six.

## 2. The triple witness

### 2.1 Statement

For N ≥ 1, let σ_N(G) be the N-fold regular subdivision of G. A divisor on V(G) is regarded as a
divisor on σ_N(G) through the original vertices.

> **Triple witness.** Let G be a connected graph of genus six, and let E be an effective divisor of
> degree three on V(G). There are an odd N ≥ 1 and an effective divisor F of degree two on σ_N(G)
> such that E + F has rank at least one on σ_N(G).

The scale N may depend on E, and the points of E may repeat. In Lean the statement is
`GenusSixExistence.tripleWitness`, for the predicate `OddCompletionWitness G 1 2` of
`GenusSixExistence/BrillNoetherRank/Reduction.lean`.

### 2.2 Descent with two residual chips

> **Lemma 2.1.** If G satisfies the triple witness, then w^1_5(G) ≥ 2.

*Proof.* Let E be effective of degree three, and take N and F from the triple witness. A vertex of
σ_N(G) lies on an edge uv of G at distance o from u, with 0 ≤ o ≤ N. Round it to the nearer of u
and v; its rounding distance min(o, N − o) is at most (N − 1)/2, because N is odd. The rounding
theorem `Spec.rank_ge_of_rank_scale_ge_nearest` (`Utilities/Subdivision/OddSubdivisionDescent.lean`)
says: let D₀ be a divisor on G, and let finitely many chips on σ_N(G) have rounding distances
adding up to less than N; if D₀ plus the chips has rank at least r on σ_N(G), then D₀ plus the
rounded chips has rank at least r on G. Apply it with D₀ = E and the two chips of F, whose
distances add up to at most N − 1. ∎

The parity of N is what lets two chips fit the budget: for even N, two chips at the midpoints of
edges cost exactly N. The form with any number of prescribed chips and two residual ones is
`Utilities.Gonality.bnRankGe_of_bnRankGe_regularSubdivision`.

### 2.3 Motivation: an odd count of nine on curves

The triple witness has a short proof by algebraic geometry, which is not formalized and is not
the proof given below. On a general curve C of genus six with general points P, Q, R, the series
K_C − P − Q − R maps C birationally onto a plane septic, and by Riemann–Roch
h⁰(P + Q + R + F) ≥ 2 exactly when F is a double point of the septic. These F form a finite scheme
of length (7 − 1)(7 − 2)/2 − 6 = 9. Nine is odd, so some point has odd residue degree N; a totally
ramified base change of degree N of a degeneration with dual graph G has dual graph σ_N(G), and
Baker's specialization lemma gives a triple witness at scale N.

### 2.4 Why a gadget needs a count

Attach to G a tripod at the three points of E: a new vertex c joined to them by three paths. The
result Γ has genus eight, and five is the Draisma–Vargas degree ⌈8/2⌉ + 1, so a regular
subdivision of Γ carries a divisor of degree five and rank one. That is not enough. Cools and
Draisma glue a tripod into a tropical morphism (§3.3): a morphism of degree four on G becomes one of
degree five on Γ, whose extra sheet is a copy of the target. Such a pencil restricts to G as a
pencil of degree four plus a chip, which says nothing about E.

On curves a count tells the two kinds apart. A rational curve attached to C at P, Q, R carries 14
limit pencils of degree five: nine contract the rational component and pass through P + Q + R,
and five come from the pencils of degree four on C. Tropically, Vargas's count gives 14 = C₄ in
genus eight and 5 = C₃ in genus six, so the members on the gadget that do not come from G have odd
total multiplicity. Tripod subtraction makes this precise.

## 3. Tripod subtraction

From here on g = 2m with m = 3, and d = m + 1 = 4 is the degree of the morphisms on G. Statements
that hold for every m are written for every m.

### 3.1 The gadget

Let G be a metric graph of genus 2m, with total edge length L(G), and let p₁, p₂, p₃ be points of
G. The *gadget* is Γ = G ∪ Y, where Y is a tripod: a new vertex c and three legs [c, p_j] of
lengths ℓ_j. It has genus 2m + 2, and the Draisma–Vargas degree in that genus is m + 2 = d + 1. The
legs are *long* if

    ℓ_j > d·L(G)      for j = 1, 2, 3.

§3–§5 take G cubic, with positive edge lengths, and the marks p_j interior to edges, so that Γ is
cubic; several marks may lie on one edge. §6 passes to the actual graph, with unit lengths and
marks at vertices, possibly repeated.

### 3.2 Members, and the count in genus eight

The objects counted are those of Draisma–Vargas, Part I, and Vargas, Part II.

* A *modification* Γ′ of Γ is Γ with finitely many metric trees grafted at points. Points of the
  grafted trees are *dangling*; the core of Γ′ is Γ.
* A *discrete tropical morphism* φ: Γ′ → T to a metric tree maps each edge e of a model of Γ′ onto
  an edge φ(e) of T with an *index* |e| ≥ 1, and e has length z_{φ(e)}/|e|, where z_t > 0 is the
  length of t. At each vertex A it is *balanced*: in each direction at φ(A), the indices of the
  edges at A add up to the index |A|. It satisfies Riemann–Hurwitz,
  r(A) := val(A) − 2 − |A|·(val φ(A) − 2) ≥ 0, and its degree Σ_{φ(A) = v} |A| does not depend
  on v.
* The *length matrix* A_φ has a row for each edge h of the core and a column for each edge t of T,
  with entry a_{ht} = Σ 1/|e| over the edges e of h above t; so length(h) = Σ_t a_{ht} z_t.
* φ is *full-dimensional* if it is change-minimal (at each vertex v of T, the change
  ch(v) = Σ_{φ(A) = v} r(A) equals 3 − val(v)) and of full rank. In genus g and degree g/2 + 1
  this is the same as A_φ being a nonsingular square matrix of size 3g − 3 (Part I,
  `lemma-practical-criteria`). The metric graphs realised by the type of φ then form the open cone
  {A_φ z : z > 0}.
* The *multiplicity* is Mult(φ) = D_φ·det A_φ / 2^{l(T)}, where D_φ is the product over the rows
  of the least common denominator of the row, and l(T) is the number of leaves of T (Part II,
  `def-multiplicity`). |Mult(φ)| is a positive integer.

A *member* over Γ is a full-dimensional φ of degree m + 2 whose open cone contains Γ, with an
identification of its core with Γ. Members are taken up to isomorphism compatible with that
identification; the isomorphism classes are the *classes* over Γ. A combinatorial type with its
labelling and core identification is a *frame*. At a request y (a vector of edge lengths for the
core), its coordinates are z = A⁻¹y; the frame is *open* at y if z > 0 and *closed* if z ≥ 0.
|Mult| is a function of the frame.

> **Count (Vargas, Part II).** Over a general metric graph of genus 2n, the members of degree
> n + 1 have total |Mult| equal to the Catalan number C_n.

The total is C₄ = 14 over a general gadget, and C₃ = 5 over a general G of genus six. The proof
uses these numbers only modulo two, through the *open odd count*: the number of open classes of
odd multiplicity, which has the parity of the total. In Lean both parities are proved, not quoted.
In genus six the open odd count in degree four is odd
(`DraismaVargas.Count.Assembly.c34_genusSix`, the count behind existence in genus six). And
`DraismaVargas.Count.EvenGenusParity` (`DraismaVargasCount/EvenGenusParity.lean`) says: for every
k ≥ 2, over every connected cubic core of genus 2k + 2 and every positive request at which no frame
has a zero coordinate, the open odd count in degree k + 2 has the parity of C_{k+1}; at k = 3 it
is even. Its proof follows the genus-six one: over the caterpillar of loops the open classes are
C_{k+1} ballot classes of multiplicity one (`DraismaVargasCount/BallotEndSwapGeneral.lean` gives
the symmetry this needs at every genus), and the parity is unchanged across walls inside a cone
and across Whitehead moves between cubic cores, by arguments written for every degree.

### 3.3 Glued members

Cools and Draisma's *gluing in a tripod*: let ψ be a member over G, of degree d, with target T_ψ,
and suppose the images u_j = ψ(p_j) are distinct interior points of target edges.

* Subdivide T_ψ at u₁, u₂, u₃, and attach at each u_j a new leaf edge, the *arm*, of length a′_j.
* Over each arm, every old sheet carries a copy of the arm, of index one.
* Add a (d + 1)-st sheet, a copy of the new target, glued at the tip of arm j to the sheet that
  carries p_j.

The result glue(ψ) is a tropical morphism of degree d + 1 from a modification of G with a tripod
attached at p₁, p₂, p₃, whose legs have lengths a_j + 2a′_j, where a_j is the distance in T_ψ from
u_j to the median of u₁, u₂, u₃. Leg j runs up arm j in the sheet of p_j, crosses to the new sheet
at the tip, comes back down, and follows the new sheet to the median, the image of c. Given leg
lengths ℓ_j, the arms have length a′_j = (ℓ_j − a_j)/2, which long legs make positive (§5.2).

In a glued member φ(c) lies in φ(G), and each leg leaves its mark up a leaf edge of T. §5 proves
that ψ ↦ glue(ψ) is a bijection, preserving |Mult|, from the classes over G onto the classes over Γ
with φ(c) ∈ φ(G). So the glued members have total C_m, which is 5 at m = 3.

### 3.4 Claw members, and the parity argument

A member over Γ is a *claw member* if φ(c) ∉ φ(G). By §4, φ(c) is then a trivalent vertex of T,
and the three edges at φ(c) are exactly the edges of T with no edge of G above them; two of them
are leaf edges, up which two of the legs make hairpins, and the third leg arrives along the third
edge. §7 shows that such a member yields E + F of rank at least one, with F of degree d − 2 = 2.

> **Dichotomy (§4.6, §4.8, §5.5).** At long legs, every member over Γ is either glued or a claw
> member, and not both.

At a general gadget with long legs,

    (open odd count over Γ) = (number of odd glued classes) + (number of odd claw classes).

The left side is even (C₄ = 14). The first term on the right is the open odd count over G, which is
odd (C₃ = 5). So the number of claw classes of odd multiplicity is odd, and in particular positive.
As integers the claw members have total |Mult| equal to C_{m+1} − C_m = 9, the count of §2.3.

§6 moves from a general gadget to the actual one, where a claw frame of odd multiplicity survives
as a closed frame, and §7 turns it into a triple witness at the odd part of its scale.

## 4. The classification at long legs

### 4.1 Set-up

Let φ: Γ′ → T be a member over Γ. It has degree d + 1 = m + 2, the tree T has 6m + 3 edges, and A_φ
is a nonsingular matrix of size 6m + 3. Its rows are the edges of Γ: the edges of G, with each edge
that carries marks split at them, and the three legs. Γ is trivalent, so every non-dangling point
of Γ′ has at most three non-dangling edges. G is connected.

* G′ is G together with every tree of Γ′ ∖ Γ grafted at a point of G, the marks included. Y′ is the
  legs and c, together with every tree grafted at c or at a point of a leg other than a mark. So
  G′ ∩ Y′ = {p₁, p₂, p₃}, and at a mark Y′ has a single germ, the leg germ.
* t_j = φ(p_j) and c* = φ(c). The leg germ at p_j lies over a target edge h_j at t_j, with index
  s_j ≥ 1. Write S = s₁ + s₂ + s₃.
* H_j is the open branch of T at t_j that contains h_j: the component of T ∖ {t_j} containing the
  interior of h_j.
* For x ∈ T not a mark image, δ_Y(x) and δ_G(x) are the degrees of Y′ and of G′ over x, counted
  with index; δ_Y + δ_G = m + 2.
* T̂ = φ(G) is a subtree of T containing every t_j, because G is connected. The *lost* edges
  L = E(T) ∖ E(T̂) are the target edges with no edge of G above them.

The following facts from Part I hold for every change-minimal morphism of full rank.

* **(leaves)** Over each leaf v of T there is exactly one non-dangling vertex. It has index 2, two
  edges, each of index 1, and r = 2. Exactly one edge of the core passes over v, and each edge of
  the core passes over at most one leaf (`rem-leaves-min-change`).
* **(dangling)** Dangling edges have index 1, and dangling vertices have r = 0
  (`lemma-dangling-no-glue`, `lemma-dangling-rphi`).
* **(paths)** A path of non-dangling vertices, none over a leaf, maps to a path of T without
  repeated vertices (`cor-edge-of-h-injection`). φ is injective on the edges of a core edge that do
  not lie over leaf edges (pass-once, `lemma-pass-once`).
* **(no return)** A non-dangling vertex not over a leaf has two non-dangling edges over distinct
  target edges (`cor-no-return`).
* **(r-formula)** For a non-dangling vertex A with nd(A) non-dangling edges,
  r(A) = nd(A) − 2 + 2|A| − Σ |e|, the sum over its non-dangling edges (`lem-rphi-nd`). Balancing
  gives |e| ≤ |A| for every edge at A.
* **(local cases)** If r(A) = 0, the non-dangling edges of A lie over distinct target edges; with
  three of them φ(A) is trivalent, and with two of them both have index |A|. If r(A) = 1 and A has
  three non-dangling edges, then φ(A) is divalent, two of the edges e₁, e₂ lie over one target edge
  and e₃ over the other, and |e₁| + |e₂| = |A| = |e₃| (`prop-local`).

### 4.2 The jump rule

> **Lemma 4.1 (jump rule).** There is an integer k₀ such that, for every x ∈ T other than t₁, t₂,
> t₃,
>
>     δ_Y(x) = k₀ + Σ_j s_j·[x ∈ H_j],      δ_G(x) = m + 2 − k₀ − Σ_j s_j·[x ∈ H_j].

*Proof.* Every point y of Y′ other than a mark has all of its germs in Y′: this is clear for the
interior points of the legs, for c, and for the points of the trees grafted on them. So φ
restricted to Y′ is balanced at y, and δ_Y is locally constant away from the mark images. At a
point t of T, compare the local degrees of Y′ in two directions e and e′ at t. Only marks over t
can make them differ, and at such a mark p_j, Y′ has a single germ, of index s_j, in direction h_j.
So the two degrees differ by Σ_{j : t_j = t} s_j·([e′ = h_j] − [e = h_j]), which is the change of
Σ_j s_j·[· ∈ H_j] between the two directions; at a point t ≠ t_j, every direction lies on the same
side of H_j. So δ_Y − Σ_j s_j·[· ∈ H_j] extends to a locally constant function on the connected
space T. The formula for δ_G follows from δ_Y + δ_G = m + 2. ∎

Glued members have k₀ = 1 and claw members k₀ = 0 (§4.7). Over a point of H₁ ∩ H₂ ∩ H₃, the degree
of G′ is m + 2 − k₀ − S; this is the degree count behind the witness of §7.

### 4.3 The shape of a leg

Write leg j as a path A₀ = p_j, A₁, …, A_μ = c of non-dangling vertices. Its interior vertices have
two non-dangling edges and its ends have three, so by (leaves) neither end lies over a leaf.

> **Lemma 4.2 (leg shape).** Exactly one of the following holds.
>
> * (i) *No detour.* φ is injective on the edges of leg j, with image the geodesic [t_j, c*]. In
>   particular t_j ≠ c*.
> * (ii) *A detour.* Exactly one interior vertex A_i lies over a leaf v of T. Let [w, v] be the leaf
>   edge. The two edges at A_i lie over [w, v], with index 1, and every other edge of the leg lies
>   over its own edge of the geodesic [t_j, c*], which passes through w. So the image is the
>   geodesic with one excursion up the leaf edge [w, v] and back.

*Proof.* If no A_i lies over a leaf, (paths) makes the image a path of T from t_j to c* without
repeated vertices: the geodesic, with at least one edge. Otherwise, by (leaves) exactly one A_i lies
over a leaf v, and 0 < i < μ; its two edges lie over [w, v] with index 1, so A_{i−1} and A_{i+1} lie
over w. By (paths), A₀, …, A_{i−1} and A_{i+1}, …, A_μ map to paths P₁ from t_j to w and P₂ from w
to c*. An edge of the leg over a leaf edge has an end over a leaf, which can only be A_i; so the
edges of P₁ and P₂ do not lie over leaf edges, and by pass-once P₁ and P₂ share no edge. Two paths
in a tree from a common vertex w with no common edge leave w along different edges, so together
they form the geodesic [t_j, c*], through w. ∎

Leg j *returns through its mark image* if (ii) holds with w = t_j: the leg leaves p_j up a leaf edge
and comes back.

> **Corollary 4.3.** c* ∈ H_j if and only if leg j does not return through its mark image.

*Proof.* If leg j does not return, its first edge is the first edge of the geodesic from t_j towards
c*, so c* lies beyond t_j in the direction h_j. If it returns, H_j is the open leaf edge of its
detour, which does not contain c*, since c* is not a leaf. ∎

> **Lemma 4.4 (detour edges are lost).** If leg j has a detour through the leaf edge [w, v], then
> [w, v] ∈ L, and leg j is the only edge of the core above v.

*Proof.* An edge of G over [w, v] would have a non-dangling end over v. By (leaves) that end is A_i,
an interior vertex of leg j, which is not on G. The second claim is (leaves). ∎

### 4.4 The lost-edge bound, and the column trick

> **Lemma 4.5 (lost-edge bound).** |L| ≤ 3. If |L| = 3, the three lost columns of A_φ span the
> coordinate space of the three leg rows.

*Proof.* For t ∈ L and a row h inside G, a_{ht} = 0, because no edge of G lies over t. So the lost
columns are supported on the three leg rows. They are columns of a nonsingular matrix, hence
linearly independent. ∎

Two consequences of nonsingularity are used repeatedly.

**Column trick.** Suppose |L| = 3. Then no two distinct columns u₁ and u₂, at most one of them lost,
agree in every row of G. Otherwise col(u₁) − col(u₂) is supported on the leg rows, hence is a
combination of the lost columns, and that is a nontrivial linear relation among the columns of A_φ:
whichever of u₁, u₂ is not lost has coefficient ±1 in it.

**Pairing.** Let u be a vertex of T with two edges u₁ ≠ u₂. Suppose every non-dangling point of G
over u has exactly two non-dangling edges, one over u₁ and one over u₂, of equal index. Then the
columns u₁ and u₂ agree in every row of G.

*Proof.* Let h be a row inside G. An edge of h over u₁ has exactly one end over u. That end is a
point of G on h with two non-dangling edges, so it is interior to h, and its other edge on h lies
over u₂ with the same index. Distinct edges over u₁ have distinct ends over u, since each such point
has only one non-dangling edge over u₁. So this is a bijection, preserving index, between the edges
of h over u₁ and over u₂, and a_{hu₁} = a_{hu₂}. ∎

### 4.5 Long legs leave the image of G

> **Lemma 4.6.** If ℓ_j > d·L(G) and leg j has no detour, then the geodesic [t_j, c*] contains a
> lost edge.

*Proof.* Suppose every edge t of the geodesic lies in T̂, and choose an edge e_t of G over each. Over
t the indices add up to d + 1, and leg j has an edge of index at least one over t, which is not
e_t; so |e_t| ≤ d. The e_t lie over distinct target edges, so they are distinct, and
Σ_t length(e_t) ≤ L(G). By Lemma 4.2(i) the leg covers each edge of the geodesic once, so

    ℓ_j = Σ_t z_t / (index of the leg over t) ≤ Σ_t z_t = Σ_t |e_t|·length(e_t) ≤ d·L(G),

a contradiction. ∎

This is the only place in §4 where the lengths of the legs enter.

### 4.6 Claw versus glued

> **Theorem 4.7.** Let φ be a member over Γ. Exactly one of the following holds.
>
> **(a) c* ∈ T̂.** If the legs are long, every leg has a detour, and L consists of the three detour
> leaf edges.
>
> **(b) c* ∉ T̂.** At any leg lengths, c* is a trivalent vertex of T, and L is the set of the three
> edges at c*: an edge f = [o, c*] with o ∈ T̂, and two leaf edges. Two of the legs have their
> detours at c*, one through each leaf edge; the third has no detour and arrives at c* along f. The
> centre c has index one. No leg returns through its mark image, so c* ∈ H₁ ∩ H₂ ∩ H₃.

*Proof of (a).* T̂ is a subtree containing t_j and c*, so it contains the geodesic [t_j, c*]. By
Lemma 4.6, a leg without a detour would have a lost edge on it; so every leg has a detour. The three
detour leaf edges are lost (Lemma 4.4) and distinct, since only one edge of the core passes over
each leaf. By Lemma 4.5 they are all of L. ∎

*Proof of (b).*

1. *The edge f.* Let U be the component of T ∖ T̂ that contains c*. Its closure meets T̂ in a single
   vertex o, because T is a tree. Each geodesic [t_j, c*] passes through o, and the edges of
   [o, c*] are lost. Let f be the edge of [o, c*] at c*. Neither o nor c* is a leaf: o lies on an
   edge of T̂ and on an edge of U, and c has three non-dangling edges.
2. *The last edges.* By Lemma 4.2 the edge of leg j at c lies over f, unless leg j has its detour at
   w = c*, in which case it lies over a leaf edge at c*, with index 1. (If the detour is at some
   w ≠ c*, the path P₂ of that proof is a nontrivial path from w to c* along the geodesic, ending
   with f.) Distinct legs with a detour at c* use distinct leaf edges (Lemma 4.4).
3. *r(c) = 0.* As c* is not a leaf, r(c) ≤ 1. Suppose r(c) = 1. By (local cases) c* is divalent,
   with edges f and f′. If no last edge lies over f′, all three lie over f, which the case r = 1
   does not allow. Otherwise f′ is a leaf edge, exactly one last edge lies over it, and it is the
   edge e₃ of the case r = 1, of index 1. Then |c| = |e₃| = 1 and |e₁| + |e₂| = 1, which is
   impossible.
4. *The claw.* So c* is trivalent, and the three last edges lie over its three edges. At most one
   lies over f, so two legs, j₁ and j₂, have their detours at c*, through the other two edges, which
   are leaf edges. The third leg, j₃, arrives along f.
5. *L.* The edges of [o, c*] and the two leaf edges are lost (Lemma 4.4), so by Lemma 4.5
   [o, c*] = f and L is the set of edges at c*. A detour on leg j₃ would add a fourth lost edge.
6. *The index of c.* With r(c) = 0, the r-formula gives |ε₁| + |ε₂| + |ε₃| = 2|c| + 1 for the last
   edges ε_i of the legs j_i, and |ε₁| = |ε₂| = 1. So |ε₃| = 2|c| − 1 ≤ |c|, and |c| = 1.
7. *No returns.* Legs j₁ and j₂ have their detours at c*, which is not t_{j₁} or t_{j₂} because
   c* ∉ T̂, and leg j₃ has no detour. By Corollary 4.3, c* ∈ H_j for every j. ∎

The members in case (b) are the claw members. A glued member is in case (a), and by §4.8 and §5.5
every member in case (a) with long legs is glued. Nothing in §4 uses genericity of G or of the
marks.

### 4.7 Leg indices, and the value of k₀

*Standing assumption:* φ is in case (b), or in case (a) with long legs. Then |L| = 3 and the column
trick applies. Two lost edges never meet at a divalent vertex: in case (b) they meet only at the
trivalent c*, and in case (a) two leaf edges at a divalent vertex would make T a path with two
edges, while T has 6m + 3 edges.

> **Lemma 4.8 (leg indices).** Under the standing assumption, every edge of every leg has index
> one. In particular S = 3.

*Proof.* Suppose the index changes along leg j at an interior vertex A, between edges e and e′. Then
A is not over a leaf, and r(A) = 2|A| − |e| − |e′| ≥ ||e| − |e′|| ≥ 1. Change-minimality gives
r(A) ≤ 1 off the leaves, so r(A) = 1, and u = φ(A) is divalent, with edges u₁, u₂ and ch(u) = 1.
Every other non-dangling point B over u then has r(B) = 0, so by (local cases) it has two
non-dangling edges, one over each of u₁ and u₂, of equal index; in particular no mark lies over u.
Pairing shows that the columns u₁ and u₂ agree on every row of G, and at most one of them is lost,
against the column trick. So the index is constant along each leg. A leg with a detour has index 1
on its leaf edge, hence everywhere; in case (b) the third leg has index 1 at c, as |c| = 1. ∎

> **Proposition 4.9 (Riemann–Hurwitz on the tripod).** For every member over Γ,
>
>     Σ r(P) = 2k₀ + S + 1,
>
> the sum running over the points P of Y′ other than the marks.

*Proof.* Y′ is a finite tree, and the marks are among its leaves. Over the vertices of a finite tree
Σ (val P − 2) = −2; each mark contributes −1, so Σ (val P − 2) = 1 over the other vertices of Y′.
For such P all germs lie in Y′, and val P − 2 = r(P) + |P|·(val φ(P) − 2). For a vertex v of T let
δ⁰(v) be the sum of |P| over the non-mark points P of Y′ over v; balancing and the jump rule give
δ⁰(v) = k₀ + Σ_j s_j·[v ∈ H_j]. Now Σ (val v − 2) = −2 over the vertices of T, and = −1 over the
vertices of H_j, since the closure of H_j is a subtree in which t_j is a leaf. So
Σ_v (val v − 2)·δ⁰(v) = −2k₀ − S, and the identity follows. ∎

> **Corollary 4.10.** Under the standing assumption, k₀ = 1 in case (a) and k₀ = 0 in case (b).

*Proof.* Evaluate the left side of Proposition 4.9. Dangling points have r = 0. A vertex A of a leg
not over a leaf has r(A) = 2|A| − 2 by Lemma 4.8, which is even and at most 1, so 0. Each detour
vertex contributes 2. At c, r(c) = 2|c| − 2 ≤ 1, so r(c) = 0. So the left side is twice the number
ν of legs with a detour, and with S = 3 the identity reads k₀ = ν − 2: ν = 3 in case (a), and ν = 2
in case (b). ∎

In case (b), k₀ = 0 can also be read off over c* directly. The points of Y′ over c* are c and, on
each of the two legs with a detour at c*, the vertex where the leg reaches c* before its excursion.
Each has index one, and no dangling tree of Y′ meets the fibre over c*. So δ⁰(c*) = 3 = k₀ + S.
This is how the formalization obtains it (§8.2).

### 4.8 The parameter count

> **Proposition 4.11.** In case (a) with long legs, each leg leaves its mark up its detour leaf
> edge: if λ_j = [w_j, v_j] is the detour leaf edge of leg j, then t_j = w_j and h_j = λ_j. The
> vertices t_j are distinct and trivalent.

There are two proofs. The first is a count of parameters: a mark must be free to move along G when
the lengths of G are fixed. The second reads the same fact off the length matrix, and it is the one
in the formalization.

*The parameter count.* Let ψ be the combinatorial type of the repaired morphism of §7.1, of degree
m + 2 − k₀ = d. By Part I's dimension formula (`prop-dim-formula`) its target, T̂ with some
divalent vertices erased, has at most 2g + 2d − 5 = 6m − 3 edges, whose lengths are sums of the
z_t. If t_j were a vertex of that target, the position of p_j along its edge of G would be linear
in those lengths, so the map from z to (the lengths of G, the position of p_j) would have rank at
most 6m − 3. But it is a projection onto 6m − 2 coordinates of the isomorphism z ↦ A_φ z. So t_j
is erased, and p_j has two non-dangling edges in ψ; if h_j lay in T̂, the copy germs of the repair
would give it a third. So h_j is a detour leaf edge, and by Lemma 4.4 it is λ_j. The same count
with two marks shows that the t_j are distinct.

*On the length matrix.*

1. w_j lies in T̂, on the geodesic [t_j, c*]. It is trivalent, with λ_j its only lost edge.
   Valence four or more is excluded by change-minimality. If w_j had only one edge in T̂, a point of
   G over w_j would have all of its non-dangling edges over that edge, which the local cases
   exclude. In particular the w_j are distinct.
2. Suppose no mark lies over w_j. Since ch(w_j) = 0, every non-dangling point of G over w_j has
   r = 0. It has no non-dangling edge over the lost λ_j, so by (local cases) it has one over each of
   the two edges of T̂ at w_j, of equal index. Pairing makes their columns agree on every row of G,
   and neither is lost, against the column trick. So some mark p_k lies over w_j.
3. At p_k, r = 0 and there are three non-dangling edges, so they lie over the three edges at w_j.
   The two edges of G at p_k do not lie over λ_j, so the leg germ does: h_k = λ_j. Then leg k passes
   over the leaf v_j, and the only edge of the core over v_j is leg j (Lemma 4.4). So k = j. ∎

Once L is known to consist of the three detour leaf edges, the second proof uses only the
nonsingularity of A_φ and the local cases; it does not use the lengths.

### 4.9 Remarks

* *Short legs.* Long legs enter only in Lemma 4.6, in case (a); case (b) holds at every leg length.
  Below d·L(G) the conclusions about case (a) can fail. In computer experiments, which are not
  part of this repository and are not used anywhere in the proof, there are members with
  φ(c) ∈ φ(G) and k₀ < 0, and members with k₀ = 0 and H₁ ∩ H₂ ∩ H₃ = ∅. So the hypothesis appears
  to be needed for the statements, not only for the proof. The bound d·L(G) is not sharp.
* *Gonality.* Corollary 4.10 bounds k₀ ≤ 1 by full rank. It can also be bounded by the theorem of
  Cools and Draisma on the dimension of the loci of metric graphs of given tree gonality: the
  repaired morphism of §7.1 has degree m + 2 − k₀, and a general metric graph of genus 2m has tree
  gonality m + 1. That route needs G general and the dimension theory of gonality loci; the
  argument above needs neither.

## 5. The gluing bijection and multiplicity

Let ψ be a member over G, of degree d, with target T_ψ. Suppose each mark p_j is an interior point
of an edge of the core of ψ, over an interior point u_j of a target edge, and that u₁, u₂, u₃ are
distinct. Write a_j for the index of ψ along the edge through p_j.

### 5.1 The construction

glue(ψ) is the construction of §3.3. Its target T′ is T_ψ subdivided at the u_j, with three arms.
Its source is a modification of G with a tripod attached at p₁, p₂, p₃ (Cools–Draisma), of genus
two more than G: the new sheet is a tree attached to the old ones at three points.

### 5.2 Positivity and change-minimality

*Positivity.* ψ is full-dimensional, so every target edge t of ψ is covered by an edge e_t of G (a
zero column would make A_ψ singular). Distinct t give distinct e_t, and
z_t = |e_t|·length(e_t) ≤ d·length(e_t), so Σ_t z_t ≤ d·L(G). Hence a_j ≤ Σ_t z_t < ℓ_j at long
legs, and a′_j = (ℓ_j − a_j)/2 > 0. The two pieces of a subdivided target edge have positive length
because the u_j are interior. So every target length of glue(ψ) is positive.

*Change-minimality.* At an old vertex of T_ψ the new sheet adds a point of index one with r = 0. At
the tip of arm j, the sheet of p_j and the new sheet form a vertex of index two with two edges of
index one and r = 2, as a change-minimal leaf requires. At u_j, now trivalent, every point has
r = 0: for p_j, with two edges of index a_j in G and the arm edge of index one, the r-formula gives
3 − 2 + 2a_j − (2a_j + 1) = 0; the other old points gain dangling arm germs; the new sheet gives a
point of r = 0.

### 5.3 The determinant

Order the rows of A_N, for N = glue(ψ), as the old rows not through a mark, the two pieces of each
row through a mark, and the three legs; order the columns as the old columns not through a u_j, the
two pieces of each subdivided column, and the three arms.

*The arm columns.* Only the hairpin of leg j passes over arm j, twice, with index one. So the column
of arm j is twice the unit vector of the row of leg j, and expanding along the arm columns gives
det A_N = ±8·det A′, where A′ is A_ψ *refined* at the three marks: p_j is declared a vertex of the
source and u_j a vertex of the target.

*One refinement.* Let B be a matrix of this kind, and refine it at one more point P, inside an edge
e₀ of index a of a row h₀, over an interior point of a target edge t₀. Column t₀ splits into t¹ and
t², and row h₀ into h¹ and h², labelled so that the part of e₀ in h¹ lies over t¹. Every source
edge over t₀ covers t₀, so it splits into two halves of equal index over t¹ and t². Hence:

* every row h ≠ h₀ has equal entries in t¹ and t², namely its old entry in t₀;
* row h¹ has entries (1/a + α, α) in (t¹, t²), and row h² has (β, 1/a + β), where α and β collect
  the other passes of h₀ over t₀;
* in every other column, the entries of h¹ and h² add up to the entry of h₀.

Replace row h² by h¹ + h², then column t¹ by t¹ − t². Column t¹ becomes 1/a times the unit vector
of row h¹, and deleting that row and column leaves B. So

    det(refined B) = ±det(B)/a,

for every row, however many times it passes over t₀, and for a mark on either pass of a hairpin.
By induction over the marks, det A′ = ±det A_ψ/(a₁a₂a₃).

### 5.4 Denominators and multiplicity

Along a row of a full-dimensional member, every index is one if the row passes over a leaf edge;
otherwise the indices are constant, or take two adjacent values k, k + 1, changing once. The least
common denominator of the row is then 1, k or k(k + 1) (Part II, `lemma-edge-deno` and
`proposition-at-most-two-weights`). Split a row inside an edge of index a: one piece has index
profile {a}, the other keeps the profile of the row, and in each case

    d(h¹)·d(h²) = d(h)·a.

Rows that are not split keep their denominators, and the leg rows, with entries one and two, have
denominator one. So D_N = D_ψ·a₁a₂a₃. The target gains three leaves, so l(T′) = l(T_ψ) + 3, and

    |Mult N| = D_ψ a₁a₂a₃ · 8|det A_ψ| / (a₁a₂a₃) / 2^{l(T_ψ)+3} = |Mult ψ|.

In particular det A_N ≠ 0, so N is full-dimensional, and it is a member over Γ.

### 5.5 The bijection

> **Theorem 5.1.** Assume long legs, and the hypotheses on the marks at the start of §5 for every
> member over G. Then ψ ↦ glue(ψ) induces a bijection, preserving |Mult|, from the classes over G
> onto the classes over Γ in case (a) of Theorem 4.7.

*Proof.*

* *Into case (a).* The centre of glue(ψ) maps to the median of the u_j, in T̂.
* *Injective.* Deleting from glue(ψ) the new sheet and the arms, and undoing the refinement at the
  marks, gives back ψ.
* *Onto.* Let φ be in case (a), with long legs. By Proposition 4.11 each leg leaves its mark up a
  leaf edge, its arm, and H_j is that arm. By Corollary 4.10 and the jump rule, δ_Y = 1 over T̂ and
  δ_Y = 2 over each arm. So over T̂, Y′ is a single sheet of index one, mapping bijectively and
  isometrically onto T̂, and over arm j it is the hairpin of leg j. The core of Y′ is the union of
  the paths in this sheet between the three hairpins, so c* is the median of t₁, t₂, t₃. Delete
  this sheet and the arms, and erase the now divalent vertices t_j. The result ψ has degree d, and
  its target has 6m − 3 edges.
  - *Full rank.* The lost columns vanish on the rows of G, so A_φ is block lower triangular, with
    diagonal blocks A_{G,T̂} and (leg rows) × L. So det A_{G,T̂} ≠ 0. Now A_{G,T̂} is A_ψ refined at
    the marks, and §5.3 gives det A_ψ ≠ 0. So ψ is full-dimensional.
  - *Open.* The coordinates of ψ are sums of coordinates of φ, so they are positive at G.
  - *Identification.* So ψ is a member over G, and glue(ψ) has the same core map as φ. A
    change-minimal member of full rank is determined by its core map: its dangling trees have index
    one and map injectively onto branches of the target, so their shape is forced. Hence
    φ ≅ glue(ψ).
* *Well defined.* The only choice in the construction is the sheet, among those of the edge through
  p_j, that carries the mark, and two choices give isomorphic glued data, by exchanging two sheets
  on the arm and at its tip. This uses that no mark lies on a loop of the core of G: a mark on a loop
  would cut it into two pieces with the same ends, and the vertex labels would not pin down the
  identification with Γ. The cubic core of §6 has no loop, so this case does not arise. ∎

## 6. Closure to the actual point

The triple witness concerns every graph G of genus six, with unit lengths, and every effective
divisor E of degree three on V(G). This section reduces it to a cubic core of genus eight at a
request with zero coordinates, and finds there a closed claw frame of odd multiplicity.

### 6.1 Contracting bridges

> **Lemma 6.1.** Let b = uv be a bridge of a graph H, and π: H → H/b its contraction. For every
> divisor D on H, r_H(D) ≥ r_{H/b}(π_*D).

*Proof.* Firing the component of H − b that contains u moves one chip from u to v, so u ∼ v. Let
k ≤ r_{H/b}(π_*D), and let E′ be effective of degree k on H. Then π_*D − π_*E′ + div s ≥ 0 for some
script s on H/b. The script s∘π is constant across b, so its divisor on H agrees with div s off
{u, v}, and its values at u and v add up to the value of div s at π(u). So D − E′ + div(s∘π) is
effective off {u, v}, with non-negative total on {u, v}, and moving chips across b makes it
effective. ∎

> **Corollary 6.2.** Let G^b be G with all of its bridges contracted. It is connected, loopless and
> bridgeless, of genus six, with no vertex of valence one. If the triple witness holds for G^b and
> π_*E, it holds for G and E.

*Proof.* At scale N each bridge of G becomes a path of N bridges of σ_N(G), and contracting all of
them gives σ_N(G^b). Lift the completion F^b to an effective F on σ_N(G) with π_*F = F^b. Then
π_*(E + F) = π_*E + F^b, and Lemma 6.1, once for each contracted edge, gives the rank. ∎

Under π a chip of E on a pendant tree moves to the vertex where the tree is attached. From here on
G is bridgeless.

### 6.2 The tripod model

*The base core.* G has a cubic model, from the reduction behind the expansion lemma
`exists_expansionModel` (`DraismaVargas/LocalCases/`). It consists of a connected cubic loopless
core G̃, with 10 vertices and 15 slots, and an expansion of G̃ onto a reduced presentation of G. In
the reduced presentation the bivalent vertices of G are suppressed, except for marker vertices that
keep it loopless, and each slot is a chain of unit edges of G. Each slot of G̃ is either contracted,
of length zero, or retained, running over one or two slots of the reduced presentation; the
contracted slots form a forest. Giving each retained slot its length and each contracted slot
length zero, and contracting, recovers G with unit lengths.

*The marks.* Write E = p₁ + p₂ + p₃. For each j choose a slot ẽ_j of G̃ and an offset s_j along it
such that the point (ẽ_j, s_j) maps to the vertex p_j:

* if p_j has valence at least three, it is a vertex of G̃ or the contraction of a subtree of the
  forest; take a slot with an end there, at offset zero or at its full length;
* if p_j has valence two, it lies inside a retained slot at an integral offset;
* repeated marks take the same slot and offset, in a fixed order, or different slots at the vertex.

*The gadget core.* Γ̃ is G̃ with each ẽ_j subdivided at its marks, together with a vertex c̃ joined
to the three mark vertices by three leg slots. It is cubic, loopless and connected, with 14 vertices
and 21 slots, so of genus 21 − 14 + 1 = 8.

*The actual request.* y_act gives the pieces of a split slot the differences of consecutive offsets,
zero allowed; the other slots of G̃ the lengths above; and the legs integers ℓ_j > 4·L(G).
Contracting its zero slots gives G ∪ Y, with unit lengths on G. Each degenerate feature of G and E
becomes a zero coordinate of y_act, or a special value of a positive one:

| feature | encoded as |
|---|---|
| a vertex of valence at least four | contracted slots of length zero |
| bivalent vertices | retained slots running over chains of unit edges |
| a mark at a vertex of valence at least three | a piece of length zero |
| a mark at a bivalent vertex | a mark inside a slot, at an integral offset |
| repeated marks | coincident offsets: a piece of length zero between two marks |

Parallel edges are allowed in cores, and unit lengths are a special but positive request.

The model must be built in this way, from G̃, and not by applying the expansion lemma to G ∪ Y.
When two marks coincide, a cubic model of G ∪ Y may join two legs at a trivalent vertex of the
forest; then the attached part contains a cycle and is not a tripod, and §4–§5 do not apply.

### 6.3 Admissible requests, and the parity of the claw classes

For a request y on the slots of Γ̃, write y_G for its G̃-part, with the pieces of each split slot
added up. Call y *admissible* if:

* (i) y > 0;
* (ii) no frame of Γ̃ in degree five has a zero coordinate at y;
* (iii) no frame of G̃ in degree four has a zero coordinate at y_G;
* (iv) for every frame of G̃, the marks avoid the points over target vertices, and their images are
  distinct;
* (v) the legs are long: ℓ_j > d·L(y_G).

Each of (ii)–(iv) asks y to avoid finitely many hyperplanes, the zero sets of nonzero linear
functionals: frame coordinates, composed with the merging map in (iii); and in (iv),
m_j s_j − m_k s_k + λ(y_G), with indices m_j, m_k ≥ 1 and independent coordinates s_j, s_k of y.
Condition (iv) follows from (ii): if a mark lay over a target vertex, or two mark images
coincided, the gluing of §5 would be a frame of Γ̃ with a zero coordinate.

At every admissible y:

* **(P1)** the open odd count over Γ̃ in degree five is even (§3.2);
* **(P2)** the open odd count over G̃ in degree four, at y_G, is odd (§3.2);
* **(P3)** every member over Γ̃ is glued or a claw member, and not both (§4);
* **(P4)** gluing is a bijection, preserving |Mult|, from the classes over G̃ onto the glued
  classes over Γ̃ (§5).

The Lean counts of §3.2 are stated at requests where no frame has a zero coordinate, which (ii) and
(iii) provide; for Part II's count, stated at general points, the open frames are locally constant
off these walls, so the counts at y equal those at a nearby general point. Together (P1)–(P4) give,
as in §3.4:

* **(P5)** at every admissible y, the number of claw classes of odd multiplicity is odd.

### 6.4 The segment

> **Theorem 6.3.** There is a frame κ over Γ̃ in degree five that is closed at y_act, has odd |Mult|,
> and is a claw frame.

*Proof.* This is the one-segment argument of the unmarked count, with more walls.

1. *A start.* Let B be the finite set of hyperplanes of (ii)–(iv). Choose w > 0 outside B; a finite
   union of hyperplanes does not cover the positive orthant.
2. *Finitely many walls.* Put y(t) = (1 − t)·w + t·y_act. Each functional of B is affine in t and
   nonzero at t = 0, so it has at most one zero, and only finitely many t ∈ [0, 1) are walls.
3. *Long legs near the end.* ℓ_j(t) − d·L(y_G(t)) is affine in t and positive at t = 1, so it is
   positive on an interval (t_L, 1].
4. *An admissible point.* Choose t₀ ∈ (t_L, 1) beyond every wall below 1. Then y(t₀) is positive,
   as a positive combination of w > 0 and y_act ≥ 0, and admissible.
5. *An odd claw class.* By (P5) there is an open claw class of odd multiplicity at y(t₀); let κ be
   its frame.
6. *Carry it to t = 1.* No coordinate of κ vanishes on [t₀, 1), so all of them stay positive there,
   and at t = 1 they are non-negative: κ is closed at y_act.
7. *Invariants.* |Mult| and being a claw frame are properties of the frame. ∎

The parity is computed at y(t₀); it is never transported along the segment.

## 7. Realisation at an odd scale

### 7.1 The repaired morphism

> **Lemma 7.1 (repair).** Let φ be a member over Γ. Let G″ be G′ with s_j disjoint copies of the
> closed branch H̄_j grafted at each mark p_j, each glued at its point over t_j and mapped onto H̄_j
> by the identity, with index one. Then φ on G′, with the identity on the copies, is a tropical
> morphism φ″: G″ → T of constant degree m + 2 − k₀, and G″ is a modification of G.

*Proof.* G′ is G with trees grafted at its points, and the copies are further trees grafted at the
marks; so G″ is a modification of G. A copy maps isometrically onto H̄_j, so its points other than
the base are balanced, with index one and r = 0. A point of G′ other than a mark keeps its germs. At
p_j, the leg germ of index s_j in the direction h_j is replaced by s_j copy germs of index one in the
same direction, so p_j stays balanced, of the same index, and its valence and r do not decrease.
Over x the copies add Σ_j s_j·[x ∈ H_j] to δ_G(x), and the jump rule gives degree m + 2 − k₀. ∎

For a claw member, k₀ = 0 and every s_j = 1, so φ″ has degree m + 2, with one copy of H̄_j at each
mark.

### 7.2 Fibres and retraction

For a balanced map ψ: X → T to a tree with nonzero indices, write D_x = Σ_{ψ(P) = x} |P|·P for the
fibre over x ∈ T.

> **Lemma 7.2 (fibres).** All the fibres D_x are linearly equivalent, and r_X(D_x) ≥ 1.

*Proof.* Fix x, x′ ∈ T, and let f(y) = d_T(x′, π(y)), where π is the nearest-point retraction of T
onto the geodesic [x, x′]. Then f has slope ±1 along the geodesic and zero elsewhere, and
div f = x′ − x. At P over y, the slope of f∘ψ along a germ g is |g| times the slope of f along the
image of g; by balancing, the order of f∘ψ at P is |P| times the order of f at y. So
div(f∘ψ) = D_{x′} − D_x. Given P in X, take x′ = ψ(P): then D_x ∼ D_{ψ(P)} ≥ P. ∎

> **Lemma 7.3 (retraction).** Let X′ be a modification of X, and ρ: X′ → X the retraction collapsing
> each grafted tree to its grafting point. Then r_X(ρ_*D) ≥ r_{X′}(D).

*Proof.* For a function f on X′, div(f|_X) = ρ_*(div f): at a grafting point a with grafted tree
S, the slopes of f into S are dropped from the order at a, and they equal minus the sum of the
orders of f on S ∖ {a}, since the two ends of each segment of S cancel. If E ≥ 0 on X has degree at
most r_{X′}(D), then D − E ∼ D′ ≥ 0 on X′, and applying ρ_* gives ρ_*D − E ∼ ρ_*D′ ≥ 0. ∎

Cools and Draisma state both facts without proof.

### 7.3 The witness divisor E + F

> **Proposition 7.4.** Let κ be a claw frame over Γ̃, closed at a request y, with coordinates z ≥ 0.
> Let Ḡ be the metric graph (G̃, y_G) with its edges of length zero contracted, and p̄_j the image of
> p_j. Let W be the retraction to Ḡ of the fibre of the repaired morphism over c*. Then
>
>     W = p̄₁ + p̄₂ + p̄₃ + F,      F ≥ 0,      deg F = m − 1,
>
> and at y = y_act, r_Ḡ(W) ≥ 1.

*Proof.*

1. *The repair is combinatorial.* The split G′/Y′, the branches H_j, the indices s_j and the copies
   of Lemma 7.1 are read off κ, and balancing at a mark is a statement about indices. So the
   repaired map is a balanced map of graphs with indices, whatever the lengths.
2. *Lengths.* Give each target edge t the length z_t ≥ 0, and each source edge e the length
   z_{φ(e)}/|e|. On the rows of the core these add up to y, because A_κ z = y.
3. *Contracting zero lengths.* The target edges of length zero form a forest, and the source edges
   of length zero are exactly those over it. Contract them one at a time; each step is a limit in
   the sense of Part II, and gives again a balanced map of graphs with indices. A merged source
   vertex C gets the index Σ |P| over its points P over any one vertex of the merged target vertex;
   balancing shows that this does not depend on the vertex. The result is a balanced map of degree
   m + 2, with nonzero indices, from a graph Ḡ″ to a tree. At y = y_act the edges of length zero in
   G̃ form a forest, so contraction keeps the genus, and Ḡ″ is a modification of Ḡ.
4. *The divisor.* By Theorem 4.7(b), c* lies in every H_j. So each copy of H̄_j has one point over
   c*, of index one, which retracts to p̄_j. The rest of the fibre is the fibre of G′ over c*, of
   degree δ_G(c*) = m + 2 − 0 − 3 = m − 1 (Corollary 4.10, Lemma 4.8); its retraction is F.
5. *Rank.* Lemma 7.2 on Ḡ″ and Lemma 7.3 give r_Ḡ(W) ≥ 1. Lemma 7.2 uses only balancing, not
   Riemann–Hurwitz, so the contraction does no harm. ∎

At the actual request, Ḡ is G with unit lengths and p̄_j = p_j, so W = E + F with F of degree two.
It remains to place W on an odd subdivision of G.

### 7.4 Odd multiplicity gives an odd scale

Let φ be the member of κ at y_act. Its *scale* N₀ is a common denominator of the target lengths z_t
and of the source lengths z_{φ(e)}/|e|; write N₀ = 2^a·u with u odd. Every vertex of the repaired
morphism lies on the (1/N₀)-grid of its edge, so W is a divisor on σ_{N₀}(G).

*Rank one on σ_{N₀}(G).* For target vertices x and x′, the function N₀·d_T(x′, π(·)) of Lemma 7.2
is an integer on the grid points and linear on each target edge, so its pullback is an integer
script on the (1/N₀)-subdivision of Ḡ″, with divisor D_{x′} − D_x; Lemma 7.3 has the same discrete
form. So the retracted fibres over the vertices of T are linearly equivalent on σ_{N₀}(G), and W is
one of them. Let R be the set of points of G over vertices of T; it contains every vertex of valence
at least three and every mark. The model of G with vertex set R has no loop: a closed path whose
interior avoids R would map into an open edge of T, locally injectively, and could not return to
its start. Its edges have lengths in (1/N₀)Z, so σ_{N₀}(G) subdivides it, and by Luo's theorem, in
its finite form for subdivisions of a loopless core, R is rank-determining. Every v ∈ R lies in the
retracted fibre over φ(v), which is equivalent to W. So W − v is winnable for every v ∈ R, and
r(W) ≥ 1 on σ_{N₀}(G).

*Odd denominators.* Let B′ be A_κ with each row multiplied by its least common denominator and each
leaf column halved: an integer matrix with |det B′| = |Mult|. Let z′ be z with its leaf coordinates
doubled. Then B′z′ is the request with each entry multiplied by its row denominator, an integer
vector, so by Cramer's rule the denominators of z′ divide |Mult|, and odd |Mult| makes them odd. No
positivity is used, so this holds at the closed point.

*Slot moments.* Fix an internal target vertex x. Along every row, the coefficient of the retracted
fibre over x at a point, times the position of the point along the row, has odd denominator (rows
that avoid the leaves use z′; rows with a hairpin use a telescoping term at the leaf). Apply this at
x = c*, which is trivalent, and restrict to the slots of G. Measure the offset of a chip along a
slot of the reduced presentation in units of 1/N₀, so that it is an integer o. Then c·o/N₀ has odd
denominator, so 2^a divides c·o, and every slot moment of F is divisible by 2^a. The chips of E sit
at vertices of the reduced presentation and do not contribute.

### 7.5 Rounding with E fixed

> **Theorem 7.5 (realisation).** Let κ be a claw frame over Γ̃ of odd |Mult|, closed at y_act, with
> scale N₀ = 2^a·u, u odd. There is an effective divisor F_u of degree two on σ_u(G) with
> r(E + F_u) ≥ 1 on σ_u(G).

*Proof.* By §7.3 and §7.4, W = E + F has rank at least one on σ_{N₀}(G), and every slot moment of F
is divisible by 2^a.

* *Interior firing on F.* The vertices of σ_u(G) are the 2^a-grid of σ_{N₀}(G), whose slots have
  lengths divisible by 2^a. On such a subdivision, an effective divisor whose slot moments are
  divisible by 2^a is linearly equivalent, by firing inside the slots, to an effective divisor of
  the same degree on the grid (`Utilities/Subdivision/InteriorFiring.lean`). Apply this to F alone,
  giving F′; then E + F′ ∼ W has rank at least one.
* *Rounding.* σ_{N₀}(G) is the 2^a-fold subdivision of σ_u(G), and the chips of F′ already lie on
  vertices of σ_u(G), at rounding distance zero. The rounding theorem of §2.2, with D₀ = E on
  σ_u(G), the two chips of F′ and budget 0 < 2^a, gives r(E + F_u) ≥ 1 on σ_u(G), where F_u is F′
  read on σ_u(G). ∎

So the triple witness holds for G at the odd scale N = u. With Corollary 6.2 it holds for every
connected graph of genus six, and with Lemma 2.1 and §1 this proves Theorem 1.

### 7.6 Remarks

* *The odd part of the scale.* N = u is the odd part of the member's own scale; if a = 0, §7.5 has
  nothing to do.
* *In examples, N = 1.* In every example computed (in experiments outside this repository; the
  observation plays no role in the proof), including marks at vertices, repeated marks,
  vertices of valence four and parallel edges, the claw members have |Mult| one, their scale is a
  power of two, and F lies on V(G) itself. An odd scale u > 1 would need an odd |Mult| of at least
  three, or a row with two edges of an odd index at least three over different target edges. The
  proof covers that case with no extra argument.

## 8. The formalization

### 8.1 Where each section is proved

`Tripod/` stands for `GenusSixExistence/BrillNoetherRank/Tripod/`, whose namespace is
`GenusSixExistence.Tripod`.

| § | content | Lean |
|---|---|---|
| 1.1 | w^r_d: `Utilities.BNRankGe`, `Utilities.bnRank` | `Utilities/Foundations/BrillNoetherRank.lean` |
| 1.2 | Theorem 1 and the triple witness: `GenusSixExistence.bnRankGe_through_six`, `GenusSixExistence.bnNumber_le_bnRank_through_six`, `GenusSixExistence.tripleWitness` | `GenusSixExistence/BrillNoetherRank.lean` |
| 1.3–1.4, 2.1–2.2 | the elementary cases, the case analysis, `OddCompletionWitness`, descent with two residual chips | `GenusSixExistence/BrillNoetherRank/Reduction.lean`, `Utilities/Subdivision/OddSubdivisionDescent.lean` |
| 1.5 | pairs in genus five | `GenusSixExistence/BrillNoetherRank/GenusFivePairs.lean`, `Utilities/Gluing/LongHandle.lean`, `GenusSixExistence/OnceMarked.lean` |
| 3.1, 6.2 | the gadget core Γ̃: subdivision at the marks, the tripod; genus, cubicity, connectedness, looplessness | `Tripod/Gadget.lean` |
| 3.2 | the parity in genus eight; the base count over the caterpillar at every genus; the count in genus six | `DraismaVargasCount/EvenGenusParity.lean`, `DraismaVargasCount/BallotEndSwapGeneral.lean`, `DraismaVargasCount/Assembly.lean` |
| 3.4, 6.3 | the claw and glued predicates; admissible requests; (P5) | `Tripod/ClawDefs.lean`, `Tripod/Classification.lean` |
| 4.3–4.6, 4.8 | leg shape, the lost-edge bound, long legs, the dichotomy, the parameter count | `Tripod/Dichotomy.lean` |
| 4.6(b), 4.7 | the shape of a claw frame, the leg indices, k₀ = 0 | `Tripod/ClawShape.lean` |
| 5 | the gluing, its determinant and multiplicity, the bijection on classes | `Tripod/Gluing.lean`, `Tripod/GluingClasses.lean` and the other `Tripod/Gluing*.lean` |
| 6.1 | contracting bridges | `Tripod/BridgeLift.lean`, `Utilities/Subdivision/BridgeLift.lean` |
| 6.2 | the tripod model | `Tripod/TripodModelDefs.lean`, `Tripod/TripodModelProof.lean`, `Tripod/TripodMarkRefinement.lean`, `Utilities/Subdivision/ScaleLift.lean` |
| 6.4 | the segment | `Tripod/Closure.lean`, `Tripod/ClosureFrame.lean`, after `DraismaVargasCount/ClosedBoundaryMember.lean` |
| 7 | the witness, rank one, odd denominators, slot moments, interior firing, rounding with E fixed | `Tripod/Realisation.lean`, `Tripod/RealisationProof.lean`, `Tripod/ChainSeparator.lean`, with `DraismaVargasCount/OddDenominator.lean`, `DraismaVargasCount/RowHairpinPosition.lean`, `DraismaVargasCount/PendantRetraction.lean`, `Utilities/Subdivision/InteriorFiring.lean`, `Utilities/Foundations/RankDeterminingSet.lean` |

`GenusSixExistence.tripleWitness` assembles the route in four steps: contract the bridges (§6.1);
build a tripod model (§6.2); find a closed claw frame of odd multiplicity (§6.4, from (P5), which
comes from the two counts of §3.2); realise it (§7).

### 8.2 Where the Lean proof differs from the prose

* **The parameter count** (§4.8) is read on the length matrix, in the second form given there: at
  the inner end of each lost leaf edge, Pairing and the column trick force a mark. Neither the
  repaired morphism nor the dimension formula is used.
* **k₀ = 0** (§4.7) is obtained by a census of the branches at the tripod over c*, not by
  evaluating Proposition 4.9: the points of Y′ over c* are listed directly, and no dangling branch
  of Y′ reaches c*.
* **The loop case** of well-definedness (§5.5) is avoided by recording that the base core G̃ of the
  tripod model is loopless, so that no mark lies on a loop slot.
* **The mark condition** (iv) of §6.3 is not imposed separately: it follows from (ii).
* **Rank one** (§7.4) is proved without building the repaired morphism as a gluing datum. The
  formalization works with the *slid fibres*: the part on G of the retracted fibre of φ over x, plus
  Σ_j [x ∈ H_j]·p_j. Restricting the pulled-back tree potential to G drops the leg germ at each mark,
  which changes its divisor by exactly the mark terms, so any two slid fibres are linearly
  equivalent. This is Lemma 7.2 for the repair, without the repair; that equivalent divisors have
  equal degree is the form of the jump rule used there.
* **The rank-determining set** of §7.4 is certified by Luo's criterion directly: every component of
  the complement of the reached set lies in a path of bivalent vertices with reached ends, and on a
  chain of the reduced presentation that closes into a loop an interior point is reached too.
* **Bridges** (§6.1) are contracted all at once, onto the fossil `Utilities.fossil G`, by a
  contraction at every scale whose fibres consist of linearly equivalent points.
* **Connectedness** of the core of G, used in §4.1, is a hypothesis of the dichotomy.

### 8.3 Statements that are not literal transcriptions

* k₀ is not defined in Lean. The predicates are *claw* (the target vertex under c is not an end of
  any target edge under an edge of G) and *glued* (for each mark, the edge of its leg at the mark
  lies over a leaf edge of the target). At long legs they are k₀ = 0 and k₀ = 1 (Corollary 4.10).
* The gluing is constructed as an operation on gluing data, and the classification states the
  bijection of §5.5 existentially: an equivalence between the open classes over G̃ and the open
  glued classes over Γ̃ that preserves multiplicity.
* The tripod model is an expansion of the marked core onto the reduced presentation of G, split at
  its bivalent marks, with Laplacian equivalences at every scale between its subdivisions and those
  of G that carry the marks to E.

## 9. References

* S. Atanasov and D. Ranganathan, *A note on Brill–Noether existence for graphs of low genus*,
  Michigan Math. J. 67 (2018).
* M. Baker, *Specialization of linear systems from curves to graphs*, Algebra Number Theory 2
  (2008), arXiv:math/0701075.
* M. Baker and S. Norine, *Riemann–Roch and Abel–Jacobi theory on a finite graph*, Adv. Math. 215
  (2007), arXiv:math/0608360.
* F. Cools and J. Draisma, *On metric graphs with prescribed gonality*, J. Combin. Theory Ser. A
  156 (2018), arXiv:1602.05542.
* J. Draisma and A. Vargas, *Catalan-many tropical morphisms to trees; Part I: Constructions*,
  arXiv:1909.12924.
* A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
  arXiv:2609.09109.
* Y. Len, *The Brill–Noether rank of a tropical curve*, J. Algebraic Combin. 40 (2014),
  arXiv:1209.6309.
* C. M. Lim, S. Payne and N. Potashnik, *A note on Brill–Noether theory and rank-determining sets
  for metric graphs*, Int. Math. Res. Not. IMRN 2012, arXiv:1106.5519.
* Y. Luo, *Rank-determining sets of metric graphs*, J. Combin. Theory Ser. A 118 (2011),
  arXiv:0906.2807.
