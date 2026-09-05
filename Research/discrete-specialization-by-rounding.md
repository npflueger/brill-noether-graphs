# Discrete specialization by rounding firing scripts

4 September 2026. This finite proof was independently audited by three
agents. Its signed core-supported winnability transfer and rank-one
consequences are now implemented in Lean, closing the six positive
genus-five constructions over their permitted contraction faces. The
arbitrary-rank inequality displayed below remains a prose theorem; it has
not been packaged as a Lean rank inequality. The argument was developed
without numerical search and uses no metric graphs, topology, or
subdivision-invariance theorem.

## 1. The finite statement

Let Q be a finite connected loopless multigraph, F a set of m edges, and
H=Q/F its loopless quotient. For the application F is a forest; the
chip-firing argument itself does not need forestness. Let G_N be obtained
from Q by keeping every edge of F at length one and replacing every other
edge by a path of N unit edges, with disjoint new interiors.

Let D be an effective divisor of degree d supported on V(Q), viewed also as
a divisor on G_N. Write pi_*D for its pushforward to H. Then

\[
 N>dm\quad\Longrightarrow\quad
 r_H(\pi_*D)\geq r_{G_N}(D).
\]

In particular, a single sufficiently stretched positive instance suffices.
The support condition is essential to the proof: it excludes chips of D in
the new interiors of the N-edge paths. D need not be chosen independently
of N if only existence on H is wanted.

## 2. A uniform bound on script differences

Fix an effective rank test E on H and lift it to an effective divisor
E_tilde on V(Q), choosing one representative in each quotient class.
Suppose f is an integer firing script on G_N with

\[
 W=D-\widetilde E+\Delta f\geq0,
 \qquad \Delta f(v)=\sum_{vw}(f(w)-f(v)).
\]

Every unit edge uv satisfies |f(u)-f(v)|<=d. To prove this when f(u)>f(v),
take the superlevel set S={x : f(x)>=f(u)}. All edges leaving S carry a
nonnegative drop. Summing effectivity over S gives

\[
 \sum_{xy\in\partial S,\ x\in S}(f(x)-f(y))
 \leq D(S)-\widetilde E(S)\leq d.
\]

The edge uv is one term of the left side. Multiplicities are counted.

The Lean proof uses a shorter equivalent argument through clamping. First
discard the effective demand, so D+Delta f is effective. At an endpoint v,
put t(x)=max(f(x)-f(v),0). Clamping preserves effectivity of D+Delta t,
and t(v)=0 with t nonnegative. The contribution of an adjacent u to
Delta t(v) bounds f(u)-f(v), while the effective coefficient
(D+Delta t)(v) is at most its unchanged total degree d. Swapping u and v
gives the absolute bound. This is
`abs_script_sub_le_deg_of_effective_sub_add_prin` in
[ScriptClamping.lean](../Utilities/Foundations/ScriptClamping.lean).
The more general `abs_script_sub_le_deg_of_le` allows a signed starting
divisor bounded pointwise by an effective divisor.

## 3. One common rounding offset

For k in {0,...,N-1}, set

\[
 q_k(x)=\left\lfloor\frac{f(x)+k}{N}\right\rfloor
 \qquad (x\in V(Q)).
\]

The following is an identity of integers, including for negative A:

\[
 \sum_{k=0}^{N-1}\left\lfloor\frac{A+k}{N}\right\rfloor=A.
\]

Indeed, write A=Nq+r with 0<=r<N. Monotonicity of floor consequently gives

\[
 \sum_{k=0}^{N-1}|q_k(u)-q_k(v)|=|f(u)-f(v)|.
\]

Sum this over the m edges of F. The total is at most dm<N. Since all
summands are nonnegative integers, some k has

\[
 \sum_{uv\in F}|q_k(u)-q_k(v)|=0.
\]

For this one offset, q_k is constant along every F-edge, hence on every
contracted component. It therefore defines an integer script phi on H.
This is a finite pigeonhole argument, not a limiting construction.

## 4. Effectivity survives the rounding

Consider an oriented edge uv of Q outside F, replaced by
x_0=u,x_1,...,x_N=v. Since both D and E_tilde vanish at its new interior
vertices, effectivity of W implies that the integer slopes

\[
 s_i=f(x_i)-f(x_{i-1}),\qquad i=1,\ldots,N,
\]

are nondecreasing. Put a=s_1 and b=s_N. Thus

\[
 Na\leq f(v)-f(u)\leq Nb.
\]

Rounding with the same offset preserves these bounds in the form

\[
 a\leq\phi(\pi v)-\phi(\pi u)\leq b.
\]

For example, the lower inequality follows from
f(v)+k>=f(u)+k+Na, using monotonicity of integer division and its exact
compatibility with addition of an integer multiple of N. The upper
inequality is identical. This works for negative slopes as well.

The original path contributes a at u and -b at v to Delta f. The coarse
edge contributes at least a at pi(u) and at least -b at pi(v) to Delta phi.
Now sum W over the old vertices in any contracted component. Contributions
of F-edges cancel in pairs. Every other endpoint contribution can only
increase on replacing f by phi. Therefore

\[
 \pi_*D-E+\Delta_H\phi\geq0.
\]

This proves the winnability implication. Apply it to every effective E of
the desired degree to obtain the rank inequality. The offset may depend
on E, as the definition of rank permits. No claim that the whole divisor
W pushes forward through a map on the path interiors is needed.

## 5. Application to a closed length cone

Let ell be a nonnegative integral length vector on one of the six cores,
with zero set F a permitted forest. First regard each surviving length-ell(e)
path as ell(e) unit edges. These intermediate unit vertices belong to Q
and carry zero chips of D. The contracted graph H is exactly the desired
closed-face graph.

Choose N>dm and apply the positive construction at lengths

\[
 \ell_N(e)=
 \begin{cases}
 1,&e\in F,\\
 N\ell(e),&e\notin F.
 \end{cases}
\]

The positive theorem's core-supported divisor is supported on V(Q), so the
finite statement applies. For the degree-four constructions on eight-vertex
cores, m<=7; **N=29 suffices uniformly for every allowed face and every
surviving integral length vector**. This is a proof parameter, not a request
to build or enumerate a graph of that size.

The proof in [GenusFiveTwoPole.lean](../LowGenus/GenusFiveTwoPole.lean)
now exposes the fixed-divisor assertions `rowXX_rank_positive` for rows
01, 02, 03, 04, 07, and 13. Each asserts rank at least one for the particular
divisor `coreDivisor s rowXXWeight`, on every positive subdivision of its
core.

[GenusFiveTwoPoleClosed.lean](../LowGenus/GenusFiveTwoPoleClosed.lean)
applies the generic specialization theorem through
`closedConstruction_of_fixed_positive_rank`. Its six
`rowXX_closedConstruction` theorems have the original
`ClosedSubdivisionDharConstruction` signatures, including every permitted
nonloopy forest face. The same weights push to `d.coreClassDivisor weight`
on those faces. This module obtains the closed statements from the shared
positive proof and generic specialization; it imports no row-specific
boundary construction.

## 6. Lean implementation and exact scope

The arithmetic and script arguments are implemented in these modules:

| Module | Role |
|---|---|
| [ScriptClamping.lean](../Utilities/Foundations/ScriptClamping.lean) | Maximum closure, normalization, clamping, and the degree bound on each script edge difference. |
| [CommonOffsetRounding.lean](../Utilities/Foundations/CommonOffsetRounding.lean) | Signed integer rounding, `sum_round`, `sum_abs_round_sub`, `exists_common_offset`, and `round_sub_bounds`. |
| [ConvexIntegerRounding.lean](../Utilities/Foundations/ConvexIntegerRounding.lean) | Telescoping path slopes, `rounded_block_slope_bounds`, and `rounded_slopes_nondecreasing`. |
| [DiscreteSpecialization.lean](../Utilities/Subdivision/DiscreteSpecialization.lean) | The consolidated subdivision transfer, rounded-script construction, common-offset specialization, and rank-one closure theorems. |

All subdivision declarations below are in the namespace
`Utilities.Certificate.DiscreteSpecialization`.

The basic formal statement is **signed core-supported winnability
transfer**. Let `weight` be any integer core weight and `majorant` a
nonnegative core weight with `weight v <= majorant v` at every vertex.
For a positive integer N satisfying

\[
 |F|\sum_v\operatorname{majorant}(v)<N,
\]

`winnable_coreClassDivisor_of_stretch` transfers winnability of
`coreDivisor (stretch d N ...) weight` to winnability of
`d.coreClassDivisor weight`. The theorem is stated on the repository's
`DegSpec` graphs, which encode loopless, genus-preserving closed faces.
It also requires that equality of representatives comes from reachability
through the actual zero-length slots. An unrelated identification of core
vertices is not allowed.

This implication constructs an actual target firing script. The theorem
`winning_script_coreClassDivisor_of_stretch` obtains a common offset and
calls `rounded_script_effective`, whose witness is `d.slotValueScript`
built from the rounded core heights and sampled path values. The proof
verifies endpoint compatibility, nonnegative interior second differences,
and the principal-divisor inequalities after summing over each contracted
class. `source_prin_classSum` and `effective_of_endpoint_comparison` in
the same module supply the quotient bookkeeping.

The formal **quantitative rank-one statement** is
`rank_ge_one_coreClassDivisor_of_stretch`: nonnegative core weights of
rank at least one on a single sufficiently stretched graph retain rank
at least one on the contracted graph. It has the same budget
`zeroCard * sum weight < N`. For each named core vertex, the proof transfers
the signed weight obtained by subtracting its chip, with the original
nonnegative weight as majorant. The identities
`coreDivisor_subChipWeight` and `coreClassDivisor_subChipWeight` verify
that the demand is exactly the required chip before and after contraction.

Finally, `rank_ge_one_coreClassDivisor_of_positive` closes a fixed
nonnegative weight that has rank at least one on every positive
subdivision. It chooses

\[
 N=\left(\sum_v\operatorname{weight}(v)\right)^{\mathrm{toNat}}
       |F|+1
\]

and invokes the single-stretch theorem. The nonnegativity of the weight
makes the conversion to a natural number exact.

The rank-one proofs transfer demands at the original core vertices and
then use the already-proved
`DegSpec.rank_ge_one_of_reaches_coreVertices` from
[DegenerateSeparator.lean](../Utilities/Subdivision/DegenerateSeparator.lean).
That separator theorem supplies rank one on the entire subdivision,
including its interior vertices. The broader arbitrary-rank argument in
Sections 1–4 is not yet a formal Lean rank inequality. In particular, the
generic signed winnability theorem should not be described as a packaged
transfer for arbitrary divisors supported at subdivision-interior vertices.

No Len semicontinuity result, topological limit, or subdivision-rank equality
is assumed as an axiom or used as a theorem dependency in this route. The
script construction and the existing core separator are the formal bridge
from the positive graph to each closed face.

## 7. Why the old interface stopped, and what this does not claim

`ScriptGluing` in
[TwoPoleReachability.lean](../Utilities/Gluing/TwoPoleReachability.lean)
assumes injective factor maps with disjoint images and a positive first
connector length. Contraction can destroy these properties. A script on
the old vertices descends only if its values agree on each contracted class.
The common offset above arranges exactly that agreement.

Arbitrary contraction of one graph does not preserve divisor rank. For
example, let Q=K_{2,3}, with degree-three vertices A,B and degree-two vertices
C,D,E. The divisor 2C is equivalent to the genus-two canonical divisor A+B,
so has rank one. Contract AC to X. The quotient has edges XB,XD,DB,XE,EB,
and the divisor becomes 2X. Burning from B first burns D,E and then X,
which has two chips but three burning incident edges. Thus 2X is B-reduced
with coefficient zero at B, and has rank zero. The large dilation N and
the support hypothesis are material assumptions of the finite statement.

Nor does the proof give descent of arbitrary existential witnesses supported
at new subdivision vertices: those chips would destroy the convexity used
in Section 4. The existing six constructions avoid this issue by furnishing
core-supported witnesses.

For comparison, [Len's paper](https://arxiv.org/abs/1209.6309) proves
upper semicontinuity of ordinary divisor rank in its universal family and
then upper semicontinuity of Brill-Noether rank. The finite argument above
addresses the ordinary-rank input needed here. It uses neither that theorem
nor a metric-to-discrete comparison theorem as a dependency.
