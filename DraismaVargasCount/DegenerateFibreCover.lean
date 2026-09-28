import DraismaVargasCount.DegenerateBigDivisor

/-!
# The pencil of fibres at the degenerate request, and a split of the rank hypothesis

This file belongs to the specialisation from cubic cores to arbitrary graphs in
the endgame of the count (step 5 of `DraismaVargasCount/Assembly.lean`).
`DegenerateBigDivisor.ForestContractionRank` is the one hypothesis of
`DegenerateBigDivisor.bnExists_of_degenerateMember`: the member's fibre divisor,
pushed to the small subdivision, has rank at least one, i.e. the member's fibre
is a `g^1_4` on the metric graph the member realizes.
`DegenerateBigDivisor.rank_pushDivisor_of_pushableRepresentatives` reduces it to
`Utilities.Certificate.GraphContractionCertificate.PushableReachabilityAtRepresentatives`
for the contraction certificate `ExpansionData.certificate`.

This file splits `PushableReachabilityAtRepresentatives` for `bigDivisor` into
**two** named obligations, proves the split, and reduces the second one to
surjectivity of the member's realization.  The endgame does not go through this
split: `CorePencilCoverProducer` proves `ForestContractionRank` from a covering
statement about the pencil and the small-side transport of
`PencilTransportProducer`.  What it uses from this file are the positivity facts
`one_le_fibre_self` and `fibre_nonneg`.

## The split

`PushableReachabilityAtRepresentatives` asks, for every vertex `b` of the small
subdivision, a *source* vertex over `b` at which `bigDivisor … root − one_chip …`
is winnable by a firing script pulled back from the small side.  The member
supplies a whole pencil of candidate divisors — the fibres
`DegeneratePlacement.fibre … root'` over the other vertices `root'` of the
member's target tree — so the two things that have to be true are:

* **(T) transport.**  `FibreTransportFrom root`: every member of that pencil
  differs from the one at `root` by a principal divisor whose script is pulled
  back from the small side.  This is
  "any two points of a tree are linearly equivalent", *plus* the requirement that
  the realizing script descend through the forest contraction.
* **(C) covering.**  `FibreCover`: every vertex of the small subdivision carries
  a chip of *some* member of the pencil.

`forestContractionRank_of_transport_cover` is the proof that (T) and (C) together
give `ForestContractionRank`, via the certificate interface.  Nothing else is
needed.

## What is proved about (C)

`fibreCover_of_realizationSurjective` reduces (C) to

    RealizationSurjective : Function.Surjective
      (ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
        DegeneratePlacement.sourcePoint …)

— the statement, in exactly the words `DegenerateBigDivisor`'s header uses, that
the images of the member's fibres **cover the small subdivision**.  The step that
makes this work is `one_le_divisor_sourcePoint`: the coefficient of
`DegeneratePlacement.divisor … raw.1.1` at `sourcePoint … raw` is at least one,
because the fibre weight there is a `SheetPartition.blockCard`, which is
positive.  So the root `root'` needed by (C) at a small vertex `b` is not
existential guesswork: it is read off the source vertex that realizes `b`.

## Scope

* **(T) is stated, not proved.**  It is stated at its exact type below.  A
  *bare* linear equivalence `bigDivisor … root ∼ bigDivisor … root'` on the big
  subdivision would **not** suffice: `PushableWinnable` demands a script of the
  form `c.pullScript tau`, i.e. one constant on contraction fibres, and the
  header of `Utilities.Iso.GraphContraction` records that the interface
  deliberately makes no rank-preservation claim.  So (T) asks for more than
  tree linear equivalence.
* **`RealizationSurjective` is not proved, and fails at large scale.**  If `D`
  has a `SlotKind.double` slot at all, the middle vertex of that slot is, by
  `ExpansionData.MarkerIsolated`, outside the image of `D.fib` altogether, so no
  branch vertex of the member can reach it and a covering argument has to use
  interior row addresses; `DegenerateRealizationImage` computes both families
  explicitly.  Moreover `DegenerateTransport` shows by counting that (C), and
  with it `RealizationSurjective`, fails as soon as the small subdivision has
  more than `Fintype.card member.target.V * degree` vertices, hence at every
  large enough scale: the pencil is indexed by the fixed target tree.
* `ForestContractionRank` is not weakened; it is consumed verbatim.
* `PushableReachabilityAtRepresentatives` is a **sufficient** condition for rank
  one after contraction, not an equivalence, so the failure of (C) is no
  evidence against `ForestContractionRank` itself.

No `sorry`, no `axiom`, no raised heartbeat limit, no `native_decide`.
-/

namespace DraismaVargas.Count.DegenerateFibreCover

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.Count.DegenerateBigDivisor
open RowRealizedPosition SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Three general facts about pushable reachability

Stated for an arbitrary contraction certificate.  None of them is about
subdivisions, and none of them assumes the certificate is `Valid`. -/

section General

universe u v

variable {G : CFGraph.{u}} {H : CFGraph.{v}} (c : GraphContractionCertificate G H)

/-- **A transported chip is a pushable removed-chip witness.**  If the pulled-back
script `tau` carries `X` to an effective divisor with at least one chip at `x`,
then `X` pushably reaches `x`.  This is the whole content of the transport half
of the split: `PushableReaches` asks for nothing else. -/
theorem pushableReaches_of_chip {X : CFDiv G} (tau : firing_script H)
    (hEff : effective (X + prin G (c.pullScript tau)))
    {x : G.V} (hChip : 1 ≤ (X + prin G (c.pullScript tau)) x) :
    c.PushableReaches X x := by
  classical
  refine ⟨tau, fun v ↦ ?_⟩
  have hEq : (X - one_chip x + prin G (c.pullScript tau)) v =
      (X + prin G (c.pullScript tau)) v - one_chip x v := by
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hEq]
  by_cases hv : v = x
  · subst hv
    simp only [one_chip_apply_v]
    omega
  · simp only [one_chip, if_neg hv, sub_zero]
    exact hEff v

/-- **A positive pushforward coefficient is a chip in the fibre.**  For an
effective divisor, positivity of the contracted coefficient at `b` produces an
actual source vertex over `b` carrying a chip. -/
theorem exists_chip_of_pushDiv_pos {Y : CFDiv G} (hEff : effective Y) {b : H.V}
    (hPos : 0 < c.pushDiv Y b) : ∃ x : G.V, c.vertexMap x = b ∧ 1 ≤ Y x := by
  classical
  by_contra hNone
  push Not at hNone
  have hZero : c.pushDiv Y b = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    by_cases hx : c.vertexMap x = b
    · have hlt := hNone x hx
      have hge := hEff x
      rw [if_pos hx]
      omega
    · exact if_neg hx
  omega

/-- **The split, at the level of the certificate interface.**  Reachability at
representatives follows from: at every target vertex, some pulled-back script
makes `X` effective with a chip somewhere in that fibre. -/
theorem pushableReachabilityAtRepresentatives_of_transportedCover {X : CFDiv G}
    (h : ∀ b : H.V, ∃ tau : firing_script H,
      effective (X + prin G (c.pullScript tau)) ∧
        0 < c.pushDiv (X + prin G (c.pullScript tau)) b) :
    c.PushableReachabilityAtRepresentatives X := by
  intro b
  obtain ⟨tau, hEff, hPos⟩ := h b
  obtain ⟨x, hx, hChip⟩ := exists_chip_of_pushDiv_pos c hEff hPos
  exact ⟨x, hx, pushableReaches_of_chip c tau hEff hChip⟩

end General


/-! ## 2.  Every source vertex carries a chip of its own fibre

This is the one positivity fact the covering half needs, and it is a statement
about `DegeneratePlacement`, not about the expansion: the coefficient of the
placed divisor at the image of a source vertex is at least the `blockCard` of
that vertex, which is positive. -/

section Chip

variable {N Q degree : ℕ} (B : Spec N Q) (y : Fin Q → ℕ)
  (member : FibreMember B.core (fun e ↦ (y e : ℚ)) degree)
  (hClosed : member.Closed)
  (hFit : ∀ e : Fin Q, memberScale member * y e ≤ B.length e)

/-- The fibre weight of a source vertex over its *own* target vertex is at least
one: it is `SheetPartition.blockCard`, which is positive (`blockCard_pos`). -/
theorem one_le_fibre_self (raw : member.data.SourceVertex) :
    1 ≤ DegeneratePlacement.fibre B y member raw.1.1 raw := by
  show (1 : ℤ) ≤ if raw.1.1 = raw.1.1 then
      ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0
  rw [if_pos rfl]
  exact_mod_cast (member.data.vertexPartition raw.1.1).blockCard_pos raw.1.2

theorem fibre_nonneg (root : member.target.V) (raw : member.data.SourceVertex) :
    0 ≤ DegeneratePlacement.fibre B y member root raw := by
  show (0 : ℤ) ≤ if raw.1.1 = root then
      ((member.data.vertexPartition raw.1.1).blockCard raw.1.2 : ℤ) else 0
  split_ifs
  · positivity
  · exact le_refl 0

/-- **The chip.**  The placed divisor of the fibre over `raw.1.1` has at least
one chip at the image of `raw`.  This is what turns "the images of the member's
fibres cover the small subdivision" into the covering obligation (C). -/
theorem one_le_divisor_sourcePoint (raw : member.data.SourceVertex) :
    1 ≤ DegeneratePlacement.divisor B y member hClosed hFit raw.1.1
      (DegeneratePlacement.sourcePoint B y member hClosed hFit raw) := by
  classical
  rw [DegeneratePlacement.divisor_apply]
  refine le_trans ?_
    (Finset.single_le_sum
      (f := fun r : member.data.SourceVertex ↦
        if DegeneratePlacement.sourcePoint B y member hClosed hFit r =
            DegeneratePlacement.sourcePoint B y member hClosed hFit raw then
          DegeneratePlacement.fibre B y member raw.1.1 r else 0)
      (fun r _ ↦ ?_) (Finset.mem_univ raw))
  · rw [if_pos rfl]
    exact one_le_fibre_self B y member raw
  · by_cases hr : DegeneratePlacement.sourcePoint B y member hClosed hFit r =
        DegeneratePlacement.sourcePoint B y member hClosed hFit raw
    · rw [if_pos hr]
      exact fibre_nonneg B y member raw.1.1 r
    · rw [if_neg hr]

end Chip


/-! ## 3.  The two obligations, at the degenerate request -/

section Obligations

variable {n p N Q degree : ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- **Obligation (T): metric-fibre transport by a descending script.**  Any two
members of the member's own pencil of fibre divisors differ by a principal
divisor whose firing script is **pulled back from the small side**, i.e. is
constant on the fibres of the forest contraction.

This is strictly stronger than `linear_equiv` of the two divisors on the big
subdivision: `GraphContractionCertificate.PushableWinnable` is defined with
`c.pullScript tau`, and the header of `Utilities.Iso.GraphContraction` says in
as many words that the interface does not assert rank preservation under
contraction.  This file states (T); it does not prove it. -/
def FibreTransportFrom (root : member.target.V) : Prop :=
  ∀ root' : member.target.V,
    ∃ tau : firing_script (small.scale k hk).graph,
      bigDivisor D small hN hL k hk member hClosed hScale root' =
        bigDivisor D small hN hL k hk member hClosed hScale root +
          prin (D.bigSpec (small.scale k hk) hN hL).graph
            ((ExpansionData.certificate D (small.scale k hk) hN hL).pullScript tau)

/-- (T) at every base point at once.  Only `FibreTransportFrom` at a single root
is ever needed; this is the uniform form, the shape "any two points of a tree
are linearly equivalent" suggests. -/
def FibreTransport : Prop :=
  ∀ root : member.target.V,
    FibreTransportFrom D small hN hL k hk member hClosed hScale root

theorem fibreTransportFrom_of_fibreTransport
    (h : FibreTransport D small hN hL k hk member hClosed hScale)
    (root : member.target.V) :
    FibreTransportFrom D small hN hL k hk member hClosed hScale root := h root

/-- **Obligation (C): the pencil covers the small subdivision.**  Every vertex of
the small subdivision carries a chip of the contracted image of *some* member of
the pencil.  `fibreCover_of_realizationSurjective` below reduces this to plain
surjectivity of the member's realization. -/
def FibreCover : Prop :=
  ∀ b : (small.scale k hk).Vertex, ∃ root' : member.target.V,
    0 < ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
      (bigDivisor D small hN hL k hk member hClosed hScale root') b

/-- **The covering obligation, in the form `DegenerateBigDivisor`'s header states
it.**  The composite of the placement with the contraction — which that header
identifies as the member's own realization — is surjective onto the small
subdivision.  `DegenerateTransport` shows that this fails at every large enough
scale. -/
def RealizationSurjective : Prop :=
  Function.Surjective
    (ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
      DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale))

/-- **(C) from surjectivity of the realization.**  Given a source vertex over `b`,
take the member of the pencil indexed by *that vertex's own* target vertex; the
chip is `one_le_divisor_sourcePoint`. -/
theorem fibreCover_of_realizationSurjective
    (hSurj : RealizationSurjective D small hN hL k hk member hClosed hScale) :
    FibreCover D small hN hL k hk member hClosed hScale := by
  classical
  intro b
  obtain ⟨raw, hraw⟩ := hSurj b
  have hmap : ExpansionData.vertexMap D (small.scale k hk) hN hL
      (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale) raw) = b := hraw
  refine ⟨raw.1.1, Finset.sum_pos' (fun v _ ↦ ?_)
    ⟨DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale) raw, Finset.mem_univ _, ?_⟩⟩
  · by_cases hv : ExpansionData.vertexMap D (small.scale k hk) hN hL v = b
    · rw [if_pos hv]
      exact bigDivisor_effective D small hN hL k hk member hClosed hScale raw.1.1 v
    · rw [if_neg hv]
  · rw [if_pos hmap]
    exact lt_of_lt_of_le Int.zero_lt_one
      (one_le_divisor_sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed
        (fit D small hN hL k hk member hScale) raw)

/-- **`ForestContractionRank` from (T) and (C).**  The contraction certificate is
`Valid` (`ExpansionData.certificate_valid`), so
`GraphContractionCertificate.rank_ge_one_pushDiv_of_pushableRepresentatives`
turns the two obligations into `ForestContractionRank` verbatim.

Read the conclusion: it is `DegenerateBigDivisor.ForestContractionRank` with the
same binders it is consumed at in `bnExists_of_degenerateMember`.  The
hypotheses `hTransport` and `hCover` are obligations *replacing* it, not extra
assumptions alongside it. -/
theorem forestContractionRank_of_transport_cover
    (hCond : D.Conditions small.core)
    (root : member.target.V)
    (hTransport : FibreTransportFrom D small hN hL k hk member hClosed hScale root)
    (hCover : FibreCover D small hN hL k hk member hClosed hScale) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root := by
  classical
  refine rank_pushDivisor_of_pushableRepresentatives D (small.scale k hk) hN hL hCond
    (bigDivisor D small hN hL k hk member hClosed hScale root) ?_
  refine pushableReachabilityAtRepresentatives_of_transportedCover
    (ExpansionData.certificate D (small.scale k hk) hN hL) (fun b ↦ ?_)
  obtain ⟨root', hPos⟩ := hCover b
  obtain ⟨tau, hTau⟩ := hTransport root'
  refine ⟨tau, ?_, ?_⟩
  · rw [← hTau]
    exact bigDivisor_effective D small hN hL k hk member hClosed hScale root'
  · rw [← hTau]
    exact hPos

/-- **The same, with (C) replaced by the surjectivity statement**: the two
hypotheses are (T) `FibreTransportFrom` and `RealizationSurjective`. -/
theorem forestContractionRank_of_transport_realization
    (hCond : D.Conditions small.core)
    (root : member.target.V)
    (hTransport : FibreTransportFrom D small hN hL k hk member hClosed hScale root)
    (hSurj : RealizationSurjective D small hN hL k hk member hClosed hScale) :
    ForestContractionRank D small hN hL k hk member hClosed hScale root :=
  forestContractionRank_of_transport_cover D small hN hL k hk member hClosed hScale
    hCond root hTransport
    (fibreCover_of_realizationSurjective D small hN hL k hk member hClosed hScale hSurj)

end Obligations


/-! ## 4.  The assembly, with `ForestContractionRank` replaced by (T) and (C) -/

/-- **`DegenerateBigDivisor.bnExists_of_degenerateMember`, with its one
hypothesis replaced by (T) and the surjectivity form of (C).**  The conclusion
and every other binder are those of `bnExists_of_degenerateMember`; only `hRank`
is replaced, by `hTransport` and `hSurj`. -/
theorem bnExists_of_degenerateMember_of_transport_realization {n p N Q : ℕ}
    (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core)
    (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    (hScale : memberScale member = 2 ^ a * u)
    (root : member.target.V) (hInternal : ¬ IsLeafVertex member.target root)
    (hTransport : FibreTransportFrom D small hN hL (2 ^ a * u) hk member hClosed hScale root)
    (hSurj : RealizationSurjective D small hN hL (2 ^ a * u) hk member hClosed hScale) :
    BNExists (small.scale u hu).graph 1 4 :=
  bnExists_of_degenerateMember small D hN hL hCond u a hu hk member hClosed hOdd hScale
    root hInternal
    (forestContractionRank_of_transport_realization D small hN hL (2 ^ a * u) hk member
      hClosed hScale hCond root hTransport hSurj)

end DraismaVargas.Count.DegenerateFibreCover
