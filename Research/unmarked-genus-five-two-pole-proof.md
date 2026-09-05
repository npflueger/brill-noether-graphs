# One proof for six unmarked genus-five constructions

4 September 2026. This note gives a uniform prose proof for the positive
subdivisions of six Atanasov–Ranganathan genus-five rows already proved in
this repository. It uses the same fixed divisors as the existing row proofs,
or their canonical residuals. The common argument has three cases, determined
by two integer firing heights and the length of one connector.

The argument is implemented in Lean as a shared construction used by the
six row consumers. A finite integer-rounding theorem now extends its fixed
core divisors to every permitted genus-preserving contraction. The
mathematical investigation used no numerical search. Implementation checks
use targeted builds with `LEAN_NUM_THREADS=4`.

## 1. Two elementary operations on firing scripts

Use the sign convention

\[
 (\Delta f)(v)=\sum_w m(v,w)\bigl(f(w)-f(v)\bigr).
\]

All scripts are integer-valued. A script wins for a divisor `R` if
`R+Delta f` is effective. Adding a constant to a script changes nothing.

If `f` and `g` win for the same divisor, their pointwise maximum also wins.
At a vertex where `f` attains the maximum, every neighboring maximum is at
least the corresponding value of `f`; hence the new Laplacian coefficient
is at least the old one. The argument with `g` is identical.

We need two precise consequences.

* **Normalize a demanded chip.** Suppose `C` is effective and `f` wins for
  `C-[p]`. Normalize `f(p)=0`, then replace `f` by `max(f,0)`. This still
  wins for `C-[p]`. At every vertex other than `p`, either the old script
  supplies the inequality, or the new value is zero and all neighboring
  values are nonnegative. At `p`, the value remains zero and all neighbor
  values have only increased. Thus the script can be chosen nonnegative
  and zero at the demanded vertex.
* **Truncate without retaining a demand.** If `C` is effective and a
  nonnegative script `f` wins for `C`, then, for every integer `a>=0`,
  `max(f-a,0)` also wins for `C`. Apply maximum closure to `f-a` and the
  zero script. If `f(p)=0`, the truncated script is still zero at `p`.

The second statement only retains effectivity for `C`; it does not promise
to retain an additional chip at `p`.

## 2. A transfer lemma at the attachment vertices

Let `A` and `B` be disjoint finite connected loopless multigraphs carrying
effective rank-one divisors `C_A` and `C_B`. Join `p in A` to `q in B` by
a path of positive integral length `L`, and join `p' in A` to `q' in B` by
a second path of positive integral length. The path interiors are disjoint
from each other and from the factors. Coincident poles within a factor,
such as `p=p'`, are allowed.

Extend `C=C_A+C_B` by zero along the connector interiors. Then `C` reaches
each attachment vertex: in particular, `C-[p]` is winnable on the joined
graph.

Choose winning scripts for `C_A-[p]` and `C_B-[q]`, and normalize them by
the first operation above. Write

\[
 f(p)=g(q)=0,\qquad f,g\geq0,\qquad
 t=f(p'),\quad s=g(q').
\]

The following three constructions give a single global script. In every
case the second connector is constant, so it contributes no principal
divisor anywhere.

### Case 1: `t<=s`

On `A`, use `f`. On `B`, use

\[
 g_t=\max\{g-(s-t),0\}.
\]

This wins for `C_B`, is zero at `q`, and equals `t` at `q'`. Use the
constant zero script on the first connector and the constant `t` script
on the second. The connector endpoint values agree with the factor
values. The left factor retains its demanded chip at `p`, and the right
factor remains effective.

### Case 2: `0<k=t-s<L`

On `A`, use `f-k`; on `B`, use `g`. The second connector is constant `s`.
Number the first connector's vertices `j=0,...,L`, from `p` to `q`, and use

\[
 h(j)=\max\{-k,j-L\}.
\]

The endpoint values are `-k` and zero. Its slopes are zero on the first
`L-k` edges and one on the last `k` edges. Therefore its contributions are

\[
 0\text{ at }p,\qquad -1\text{ at }q,\qquad
 +1\text{ at the interior vertex }j=L-k,
\]

and zero everywhere else. The factor residuals are respectively
`C_A-[p]+Delta f` and `C_B-[q]+Delta g`, both effective. The connector's
new chip is effective as well. All heights and the bend position are
integers.

### Case 3: `t-s>=L`

Put

\[
 f_* = \max\{f-(t-s-L),0\}.
\]

It wins for `C_A`, is zero at `p`, and has value `s+L` at `p'`. Use
`f_*-L` on `A`, `g` on `B`, the constant `s` on the second connector,
and `h(j)=j-L` on the first connector. The first connector contributes
`+1` at `p`, `-1` at `q`, and zero internally. At `p`, its incoming chip
pays for the demanded `-[p]`. Thus the factor inequalities reduce to

\[
 C_A+\Delta f_*\geq0,\qquad
 C_B-[q]+\Delta g\geq0.
\]

This proves that `C` reaches `p`. Swap the two factors or exchange the
roles of the two connectors to reach every attachment vertex.

The lemma only proves reachability of the attachment vertices. It does
not assert that arbitrary factor pencils automatically give rank one
everywhere on the joined graph. The following application supplies the
remaining rank tests separately.

## 3. The canonical divisor application

Let `G` be a positive integral subdivision of a connected loopless cubic
genus-five core. Suppose deleting the interiors of two subdivided core
edges leaves two connected, leafless genus-two factors `A,B`. These are
additional hypotheses on the cut, checked for each of the six applications.
Retain the two removed paths as the connectors in Section 2.

Set

\[
 C=K_A+K_B.
\]

Leaflessness makes both canonical divisors effective. Each has degree two
and rank one by Riemann–Roch. Every original cubic core vertex other than
the attachment poles retains valence three in its factor and therefore
already carries one chip of `C`. Section 2 reaches all attachment poles.

The embedded vertices of a loopless core form a strong separator on every
positive subdivision, so reaching all of them proves

\[
 \deg C=4,\qquad r_G(C)\geq1.
\]

The repository's existing final step is
`Utilities.Certificate.CoreVertexReachability.bnExists_of_reaches_coreVertices`
in [CoreVertexReachability.lean](../Utilities/Subdivision/CoreVertexReachability.lean).
Thus the argument does not require a new rank-determining theorem.

There is also a useful canonical dual. Counting the two added incidences
on each factor gives

\[
 K_G=C+[p]+[p']+[q]+[q'].
\]

Since `g(G)=5` and `deg C=4`, Riemann–Roch implies

\[
 r_G(C)=r_G\bigl([p]+[p']+[q]+[q']\bigr)\geq1.
\]

Consequently both the factor-canonical divisor and the divisor on the
four attachment poles are uniform degree-four pencils.

## 4. The six current row instances

The cut slots and vertex labels below refer to the actual incidence tables
in [GenusFiveCoreAtlas.lean](../LowGenus/GenusFiveCoreAtlas.lean). Each
listed side has four vertices and five internal slots, hence genus two;
inspection of those tables also gives connectedness and leaflessness.

| Row | Cut slots and endpoints | Vertex set of one factor | Earlier displayed support | Which divisor |
|---|---|---|---|---|
| 01 | `5: 3–5`, `7: 2–4` | `{0,1,2,3}` | `{2,3,4,5}` | Four poles |
| 02 | `0: 0–1`, `2: 2–5` | `{1,2,3,4}` | `{0,1,2,5}` | Four poles |
| 03 | `5: 2–6`, `7: 3–7` | `{0,1,2,3}` | `{0,1,4,5}` | `K_A+K_B` |
| 04 | `2: 1–4`, `8: 7–3` | `{0,1,2,3}` | `{0,2,5,6}` | `K_A+K_B` |
| 07 | `5: 0–4`, `6: 1–5` | `{0,1,2,3}` | `{2,3,6,7}` | `K_A+K_B` |
| 13 | `10: 0–4`, `11: 1–5` | `{0,1,2,3}` | `{2,3,6,7}` | `K_A+K_B` |

No classification of the individual genus-two factors into theta or
dumbbell shapes is needed for this proof.

The current consumer is
[GenusFiveConstructions.lean](../LowGenus/GenusFiveConstructions.lean).
Its six corresponding declarations are `row01_firstFamily`,
`row02_secondFamily`, `row03_straightforward`, `row04_fourthFamily`,
`row07_straightforward`, and `row13_straightforward`. These ledger entries
use the [shared closed theorem](../LowGenus/GenusFiveTwoPoleClosed.lean).
That theorem extends the fixed divisor from the
[positive construction](../LowGenus/GenusFiveTwoPole.lean) by discrete
specialization, without importing any of the six old row modules.
These constructions feed the existing unconditional
`AtanasovRanganathan.brillNoetherExistenceThroughFive` in
[AtanasovRanganathanExistence.lean](../LowGenus/AtanasovRanganathanExistence.lean).

## 5. Boundary cases and implementation scope

* **Equal firing heights.** If `t=s`, Case 1 applies with no truncation.
* **Equality with the connector length.** If `t-s=L`, Case 3 applies with
  `f_*=f`. The bend has reached an endpoint, and the linear connector
  supplies exactly the stated endpoint contributions.
* **Unit connector.** For `L=1`, Case 2 contains no integer value of `k`.
  Cases 1 and 3 cover everything. The second connector may independently
  have length one because its script is constant.
* **Coincident poles.** If `p=p'`, then `t=0`, so only Case 1 can occur.
  If `q=q'`, then `s=0`; the same formulas remain consistent at that
  shared vertex. If both coincidences hold, `t=s=0`. In the cubic
  leafless application, two distinct cut slots cannot meet at the same
  vertex within one factor: deleting both would leave valence one there.
  Thus the six positive row instances have four distinct poles.
* **Degree-two subdivision vertices.** They contribute zero to the factor
  canonical divisors. Reachability of the original loopless core still
  gives rank one on the entire subdivision.

The direct two-pole script interface assumes **positive** connector lengths
and positive subdivisions of the factors. The consumer `RowConstruction`
in `GenusFiveConstructions.lean` also includes every permitted zero-length
forest face. These stronger obligations now follow from
[discrete specialization](../Utilities/Subdivision/DiscreteSpecialization.lean).
For an effective degree-four core divisor and a zero set F, use the positive
construction with zero slots assigned length one and surviving lengths
multiplied by N>4|F|. A common rounding offset makes a winning script constant
on the zero-slot components, and endpoint slope comparisons prove effectivity
on the quotient. The exact closed-orthant consumer statements are preserved.

The boundary issue is more than a zero-length endpoint formula. In row 13,
contracting slots `{0,1,10,11}` identifies the tree `4–0–2–1–5`. This is an
allowed nonloopy forest face, but it identifies two vertices of the original
right factor without contracting a right-factor edge. Thus the factor
embeddings used in the positive proof need not survive. This obstructs that
particular interface, not the divisor's rank. Integer rounding constructs a
script that agrees throughout every contracted class. In this specific
row-13 example the pushed divisor even has one chip on each remaining core
class, so its rank follows directly from the existing separator theorem.

## 6. Implementation map

- [ScriptClamping](../Utilities/Foundations/ScriptClamping.lean) proves
  maximum closure, truncation, and normalization at a demanded chip.
- [TwoPoleReachability](../Utilities/Gluing/TwoPoleReachability.lean) proves
  the three cases against an explicit script-gluing interface, including
  the symmetric right-pole conclusion.
- [CanonicalDivisor](../Utilities/Subdivision/CanonicalDivisor.lean) reuses
  the existing valence formulas and Riemann–Roch for the factor pencils.
- [TwoPoleSubdivision](../Utilities/Subdivision/TwoPoleSubdivision.lean),
  and its [principal identities and gluing realization](../Utilities/Subdivision/TwoPoleSubdivisionGluing.lean)
  construct actual global scripts from finite incidence data; the abstract
  gluing interface is discharged, not left as a hypothesis of the row results.
- [GenusFiveTwoPoleData](../LowGenus/GenusFiveTwoPoleData.lean) checks the
  six rows' incidence tables, factor connectedness, leaflessness, canonical
  weights, and attachment-vertex coverage.
- [GenusFiveTwoPole](../LowGenus/GenusFiveTwoPole.lean) assembles the common
  positive proof, using the existing core-reachability theorem.
- [DiscreteSpecialization](../Utilities/Subdivision/DiscreteSpecialization.lean)
  proves signed core-supported winnability transfer and the quantitative
  rank-one consequence. The integer arithmetic is in
  [CommonOffsetRounding](../Utilities/Foundations/CommonOffsetRounding.lean)
  and [ConvexIntegerRounding](../Utilities/Foundations/ConvexIntegerRounding.lean).
- [GenusFiveTwoPoleClosed](../LowGenus/GenusFiveTwoPoleClosed.lean) supplies
  all six complete closed constructions to the ledger.

The shared positive proof uses `K_A+K_B` for all six rows. For rows 01 and 02
this chooses the canonical residual of the old displayed four-pole divisor;
the existence statements do not require a particular support. The closed
proof now uses these same weights on every contraction face. The
[rounding note](discrete-specialization-by-rounding.md) gives the finite
argument, its formal APIs, and its support restriction.

## 7. Verification

The positive and closed-row targets have passed four-thread builds. For
focused development use `LEAN_NUM_THREADS=4 lake build
LowGenus.GenusFiveTwoPoleClosed`; after changing integration or the library
roots use `LEAN_NUM_THREADS=4 lake build Utilities LowGenus`.
Both affected library roots have also passed after replacing the six old
proofs. The [comparison note](genus-five-proof-comparison.md) records the
source-size and compilation measurements that supported their retirement.
The [axiom audit](genus-five-specialization-axioms.txt) confirms that the
specialization theorem, six closed-row results, and public existence theorem
use only `propext`, `Classical.choice`, and `Quot.sound`.

The row-13 boundary example above was also checked by Lean's kernel:
`{0,1,10,11}` is a forest, is not loopy, and connects vertices `4` and `5`
under `ReachIn`. Thus the contraction limitation is supported by a verified
example, rather than inferred from a drawing.
