# The long-handle lemma

Attach a long path between two vertices of a graph. A divisor of rank at least one on the new
graph gives a divisor of the same degree and rank at least one on the old graph, with a chip at
each of the two vertices. The statement is formalized as
`Utilities.exists_pencil_through_ends_of_handle` in
[`Utilities/Gluing/LongHandle.lean`](../Utilities/Gluing/LongHandle.lean). This note gives the
proof in prose.

## 1. Statement

Let G be a finite connected loopless multigraph, x and y two of its vertices, and d an integer.
Let k = m + 2 with m even. Let G_k be G together with new vertices p_1, …, p_{k−1} and new edges
p_{i−1}p_i for 1 ≤ i ≤ k, where p_0 = x and p_k = y. Write μ = p_{k/2} for the midpoint. Suppose
the handle is long:

    2 d (|V(G)| − 1) < k.

> **Long-handle lemma.** If G_k has a divisor of degree d and rank at least one, then G has an
> effective divisor of degree d and rank at least one with a chip at x and a chip at y.

When x ≠ y the divisor contains x + y. In Lean, G_k is `handleGraph G x y m`.

The algebraic picture is a node. A curve with two points x and y identified carries a pencil
exactly when its normalization carries one with x and y in a common fibre. A long path plays the
part of the node. The companion statement for one point, with 2x in place of x + y, attaches a
cycle at x; it is `Utilities.bnExists_vertexWedge_one_iff`.

The lemma is meant to be used with an existence theorem one genus up. A connected graph of genus
five with a handle has genus six, and Brill–Noether existence in genus six
(`GenusSixExistence.criticalPencil`) gives the handle graph a divisor of degree four and rank at
least one. So any two distinct vertices of a connected graph of genus five lie on an effective
divisor of degree four and rank at least one.

## 2. Notation

A script is an integer function σ on vertices, with

    div σ(v) = Σ_{w ∼ v} (σ(w) − σ(v)),

the sum running over the edges at v. Two divisors are equivalent when they differ by some div σ.
For a script σ on G_k put s_i = σ(p_i) − σ(p_{i−1}) for 1 ≤ i ≤ k. Then

* div σ(p_i) = s_{i+1} − s_i for 0 < i < k;
* s_1 + … + s_k = σ(y) − σ(x);
* for v in V(G): div_{G_k} σ(v) = div_G(σ|_G)(v) + [v = x] s_1 − [v = y] s_k.

For a divisor E on G_k, write E|_G for its restriction to V(G). The chips of E on p_1, …, p_{k−1}
are its handle chips; a handle chip at p_i has position i.

## 3. Proof

**(a) A script moves little on G.** Let E be effective of degree d on G_k, let w be a vertex of
G, and let σ be a script with E − w + div σ effective. Then |σ(u) − σ(v)| ≤ d for every edge uv
(`Utilities.abs_script_sub_le_deg_of_effective_sub_add_prin`). A function on a connected graph
that changes by at most d along each edge changes by at most d (|V| − 1) between any two
vertices: the sets {v : σ(v) ≥ σ(u) − j d} grow strictly with j until they are everything. Hence

    |σ(x) − σ(y)| ≤ d (|V(G)| − 1) < k/2.

**(b) Restriction.** Let E be effective of degree d on G_k with rank at least one and at most
one handle chip, at position b if there is one. Define a divisor E° on G:

* E° = E|_G if there is no handle chip;
* E° = E|_G + x if b ≤ k/2, and E° = E|_G + y if b > k/2.

Then E° has rank at least one on G. If b = k/2, then E|_G has rank at least one on G as well.

*Proof.* Fix a vertex w of G and a script σ with E − w + div σ effective. At a handle vertex,
effectivity says s_{i+1} − s_i ≥ −E(p_i). So the slopes are nondecreasing, except for one
possible drop by 1 after index b. Compare with (a):

* No handle chip, or b ≥ k/2: if s_1 ≥ 1, then s_i ≥ 1 for i ≤ k/2 and s_i ≥ 0 after, so the
  slopes sum to at least k/2. So s_1 ≤ 0.
* b < k/2: if s_1 ≥ 2, then s_i ≥ 1 throughout and the sum is at least k. So s_1 ≤ 1.
* No handle chip, or b ≤ k/2: if s_k ≤ −1, then s_i ≤ −1 for i > k/2 and s_i ≤ 0 before, so
  the sum is at most −k/2. So s_k ≥ 0.
* b > k/2: if s_k ≤ −2, the sum is at most −k. So s_k ≥ −1.

By the third formula of §2, on V(G)

    E|_G − w + div_G(σ|_G) = (E − w + div σ)|_G − s_1 · x + s_k · y.

In each case the chip that E° adds makes the right side effective. So E° − w is equivalent on G
to an effective divisor, for every w. ∎

**(c) Spreading.** Let E be effective on G_k with handle chips at positions a ≤ c (two chips at
p_a if a = c). The set {p_a, …, p_c} can fire: only its two ends have an edge leaving it. Firing
moves one chip from p_a to p_{a−1} and one from p_c to p_{c+1}. Chips strictly between do not
matter. The sum of the two positions does not change, counting x as position 0 and y as
position k. The quantity Σ p (k − p) over the handle chips drops by at least 2, so the process
stops.

Repeating this while two handle chips remain, E is equivalent to an effective divisor

    E¹ = E|_G + α x + β y + (at most one handle chip, at position b).

If E has n handle chips, with positions summing to M, then M = k β + b and α + β + [b > 0] = n.
Here b = 0 means that no handle chip is left.

**(d) The end.** Let D have degree d and rank at least one on G_k. Take an effective E
equivalent to D with a chip at μ, and let n ≥ 1 and M be as in (c).

*n = 1.* The only handle chip is at the midpoint. By (b), E|_G has rank at least one on G, in
degree d − 1. Take an effective F equivalent to it on G with a chip at x. Then F + y has degree
d, rank at least one, and a chip at x and at y.

*n ≥ 2.* Form E¹ and apply (b) to it. The result is E″ = E|_G + α′ x + β′ y of rank at least one,
where β′ = β + [b > k/2] and α′ = n − β′. One handle chip of E is at k/2 and the others are in
[1, k − 1], so k/2 < M < (n − 1/2) k.

* b = 0: β = M/k is an integer strictly between 1/2 and n − 1/2. So 1 ≤ β ≤ n − 1.
* 0 < b ≤ k/2: k β = M − b > 0, so β′ = β ≥ 1; and α′ = α + 1 ≥ 1.
* b > k/2: β′ = β + 1 ≥ 1; and k β = M − b < (n − 1) k, so β ≤ n − 2 and α′ = α ≥ 1.

In every case α′ ≥ 1 and β′ ≥ 1, so E″ has a chip at x and a chip at y. ∎

## 4. Remarks

* **The first case of (d) is real.** It is the case in which G itself carries a pencil of degree
  d − 1 and the handle carries one more sheet. Pushing every handle chip to its nearer end does
  not give a chip at both ends there.
* **The midpoint.** The representative must have a chip at the midpoint. From a chip elsewhere
  the inequalities of (d) can fail: all the handle chips can leave at the same end.
* **One chip in (b).** With two handle chips (b) is false as stated: a symmetric pair goes to x
  and to y, one each, whichever halves the chips lie in. Spread first.
* **Length.** Some length is needed. Let G be two digons {a, a′} and {b, b′} joined by a path
  a — c — b, and take x = a, y = b′, d = 2. On G the divisors of degree two and rank one are the
  canonical ones, and none has a chip at both x and y. Attach a handle x — q — y of two edges
  (m = 0). The new graph has genus three, and 2x has rank one on it. So the lemma fails for a
  handle of two edges. A search over all connected multigraphs with at most five vertices and
  eight edges, in degrees two and three, found failures only for handles of at most two edges,
  and none for three or four. The least length that suffices is not known; the bound in the
  statement is what the proof of (b) uses.
* **Coincident ends.** The Lean statement does not assume x ≠ y. If x = y the handle is a cycle
  through x, and the conclusion is only that x carries a chip.

## 5. The Lean development

| module | content |
|---|---|
| `Utilities/Gluing/HandleGraph.lean` | `handleGraph`, its edge multiplicities, `div σ` at an old vertex and at a handle vertex (`prin_handleGraph_inl`, `prin_handleGraph_point`), `genus_handleGraph`, `graph_connected_handleGraph`, and the number and moment of the handle chips |
| `Utilities/Gluing/HandleRestriction.lean` | steps (a) and (b): `sub_le_mul_card_sub_one_of_edge_bound`, `rank_handleRestrict_ge_one_of_interior_zero`, `rank_handleRestrict_ge_one_of_single_chip` |
| `Utilities/Gluing/HandleSpread.lean` | step (c): `exists_collapsed_representative` |
| `Utilities/Gluing/LongHandle.lean` | step (d): `exists_pencil_through_ends_of_handle` |

The vertices of `handleGraph G x y m` are written `handleInl a` for a vertex a of G and
`handleInr i` for the new vertex at position i + 1. The handle has m + 2 edges, and the lemma
asks for m even and `2 * (d * (|V(G)| - 1)) < m + 2`.
