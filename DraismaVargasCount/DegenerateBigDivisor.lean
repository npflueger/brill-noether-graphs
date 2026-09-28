import DraismaVargasCount.DegeneratePlacement
import DraismaVargasCount.ExpansionSeriesMoment

/-!
# The big-side divisor at the degenerate request

The geometric half of the endgame for a graph whose cubic model contracts a forest.
`Count/DegeneratePlacement.lean` places a member on a target `Spec` it only partly fills.
This file is the instance the endgame (step 5 of `Assembly`) uses: the target is
`D.bigSpec (small.scale k hk) hN hL`, and the request is the **degenerate** one -- the
small-side slot lengths on the retained slots and `0` on the contracted (forest) slots.

## The two lengths that disagree, and why that is harmless

`(D.bigSpec T hN hL).length e` is `kindLength T (D.kind e)`, which is `1` on a
contracted slot, because `Spec.length_pos` forbids `0`.  `degenerateLength`
is `0` there.  So the member's realized length of a contracted slot falls
**short** of the room `D.bigSpec` gives it, by exactly one unit: the positivity
`Spec.length_pos` constrains the placement from both ends.

`DegeneratePlacement` was written to tolerate exactly that: `fit` supplies its
`hFit`, and `exact` supplies its `hExact` on the slots where it is used -- a slot
with an interior vertex has length at least two, so it is not contracted, and
there `degenerateLength` **is** the exact scaled length.  A contracted slot has
no interior vertex of `D.bigSpec` at all, so the odd-denominator condition is
empty there rather than failing.

## What is proved

* `degenerateLength`, `kindLength_scale_of_ne_contracted`, `fit`, `exact` -- the
  request and the two inequalities `DegeneratePlacement` asks for.
* `bigDivisor` -- the divisor itself, a literal pushforward of the member's own
  pullback fibre; `bigDivisor_effective`, `bigDivisor_degree`,
  `bigDivisor_interior_mem` -- the hypotheses `hEff`, `hDeg` and `hBig` of
  `bnExists_of_bigDivisor`.
* `bnExists_of_degenerateMember` -- the assembly, with `ForestContractionRank` as its one
  remaining hypothesis; `exists_odd_scale_bnExists_of_degenerateMember` is the
  same with the odd part of the member's own scale extracted.
* `pushDivisor_bigDivisor` -- **what `ForestContractionRank` is a statement about.**  The
  small-side divisor whose rank it asks for is the pushforward of the member's
  own pullback fibre along one map, `vertexMap ∘ sourcePoint`, from the member's
  source graph onto the small subdivision.
* `rank_pushDivisor_of_pushableRepresentatives` -- **`ForestContractionRank` reduced to
  an interface of `Utilities`.**  `ExpansionData.vertexMap` is
  `Utilities.Certificate.CoreExpansion`'s own contraction certificate, which is valid
  (`certificate_valid`), and
  `GraphContractionCertificate.rank_ge_one_pushDiv_of_pushableRepresentatives`
  turns `PushableReachabilityAtRepresentatives` into the rank hypothesis.  So the rank
  statement need not be attacked as "rank is upper semicontinuous under contraction"
  in the abstract: it is the statement that the member's fibre divisor reaches
  one representative of every contraction fibre by a script pulled back from the
  small side.

## What is not proved here: `ForestContractionRank`

`ForestContractionRank` below is a hypothesis of the assembly in this file.  It is proved
for the members the endgame uses in `CorePencilCoverProducer`
(`CorePencilCoverProducer.forestContractionRank_of_markerFreePencilCover`, with the pencil
transport of `PencilTransportProducer`).  It is not implied by
`DegeneratePlacement.divisor_effective` or `..._degree`, and it is not a positivity
statement about the count: it is about rank.

`pushDivisor_bigDivisor` pins down what it is a statement about: the composite
`vertexMap ∘ sourcePoint` is the member's own realization (exactly so on a retained slot;
on a contracted slot both ends of the re-inserted unit edge go to one small core vertex,
so exactly so there too).  So `ForestContractionRank` says the member's fibre is a
`g^1_4` on the metric graph the member realizes, and it is not a free-standing
"rank is upper semicontinuous under contraction" theorem.

What discharges it, in the shape the interface of `Utilities` wants: for every
vertex of the small subdivision, a source vertex over it at which
`bigDivisor … root - one_chip …` is winnable by a firing script pulled back from
the small side.  The member supplies a whole `ℙ¹` of candidates -- the fibres
`DegeneratePlacement.fibre B y member root'` over the other target vertices
`root'`, all linearly equivalent because any two points of a tree are -- and the
remaining step is that their images cover the small subdivision, which
`CorePencilCoverProducer` carries out, moving markers where necessary.
-/

namespace DraismaVargas.Count.DegenerateBigDivisor

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource
open RowRealizedPosition SlotMoment
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {n p N Q degree : ℕ}

/-! ## 1.  The degenerate request on the expanded core -/

/-- **The degenerate request.**  A retained big slot asks for the small-side
length its role forces; a contracted one asks for `0`.  This is not a `Spec`
length assignment and cannot be: `Spec.length_pos` forbids the zero. -/
def degenerateLength (D : ExpansionData n p N Q) (small : Spec n p) (e : Fin Q) : ℕ :=
  if D.kind e = SlotKind.contracted then 0 else kindLength small (D.kind e)

theorem degenerateLength_contracted (D : ExpansionData n p N Q) (small : Spec n p)
    {e : Fin Q} (h : D.kind e = SlotKind.contracted) :
    degenerateLength D small e = 0 := by
  simp [degenerateLength, h]

theorem degenerateLength_of_ne (D : ExpansionData n p N Q) (small : Spec n p)
    {e : Fin Q} (h : D.kind e ≠ SlotKind.contracted) :
    degenerateLength D small e = kindLength small (D.kind e) := by
  simp [degenerateLength, h]

/-- Scaling multiplies every **non**-contracted kind length by the scale.  It
does not multiply the contracted one, which stays `1`: that is the mismatch
this file is organised around. -/
theorem kindLength_scale_of_ne_contracted (small : Spec n p) (k : ℕ) (hk : 0 < k)
    {kind : SlotKind p} (h : kind ≠ SlotKind.contracted) :
    kindLength (small.scale k hk) kind = k * kindLength small kind := by
  cases kind with
  | contracted => exact absurd rfl h
  | single j => simp [kindLength, Spec.scale_length]
  | double j₁ j₂ =>
      simp only [kindLength, Spec.scale_length]
      ring

/-! ## 2.  The two hypotheses `DegeneratePlacement` asks for -/

section Receipts

variable (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)

/-- **The fit.**  The member never overruns the room `D.bigSpec` gives it: it
fills a retained slot exactly and falls one unit short on a contracted one. -/
theorem fit (member : FibreMember D.bigCore
      (fun e ↦ (degenerateLength D small e : ℚ)) degree)
    (hScale : memberScale member = k) (e : Fin Q) :
    memberScale member * degenerateLength D small e ≤
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  have hlen : (D.bigSpec (small.scale k hk) hN hL).length e =
      kindLength (small.scale k hk) (D.kind e) := rfl
  rw [hScale, hlen]
  by_cases h : D.kind e = SlotKind.contracted
  · rw [degenerateLength_contracted D small h, Nat.mul_zero]
    exact Nat.zero_le _
  · rw [degenerateLength_of_ne D small h, kindLength_scale_of_ne_contracted small k hk h]

/-- **The exactness, where it is used.**  A big slot with an interior vertex has
length at least two, hence is not contracted, hence is filled exactly. -/
theorem exact (member : FibreMember D.bigCore
      (fun e ↦ (degenerateLength D small e : ℚ)) degree)
    (hScale : memberScale member = k) (e : Fin Q)
    (hTwo : 1 < (D.bigSpec (small.scale k hk) hN hL).length e) :
    memberScale member * degenerateLength D small e =
      (D.bigSpec (small.scale k hk) hN hL).length e := by
  have hlen : (D.bigSpec (small.scale k hk) hN hL).length e =
      kindLength (small.scale k hk) (D.kind e) := rfl
  rw [hlen] at hTwo ⊢
  rw [hScale]
  by_cases h : D.kind e = SlotKind.contracted
  · rw [h] at hTwo
    exact absurd hTwo (by simp [kindLength])
  · rw [degenerateLength_of_ne D small h, kindLength_scale_of_ne_contracted small k hk h]

/-! ## 3.  The divisor, and the three hypotheses `bnExists_of_bigDivisor` wants -/

variable (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) degree)
  (hClosed : member.Closed) (hScale : memberScale member = k)

/-- **The big-side divisor at the degenerate request.**  A literal finite
pushforward of the member's own original pullback fibre along the placement of
`Count/DegeneratePlacement.lean`; nothing is chosen existentially, and no
positivity of the request is used. -/
noncomputable def bigDivisor (root : member.target.V) :
    CFDiv (D.bigSpec (small.scale k hk) hN hL).graph :=
  DegeneratePlacement.divisor (D.bigSpec (small.scale k hk) hN hL)
    (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale) root

theorem bigDivisor_effective (root : member.target.V) :
    effective (bigDivisor D small hN hL k hk member hClosed hScale root) :=
  DegeneratePlacement.divisor_effective _ _ _ _ _ _

theorem bigDivisor_degree (root : member.target.V) :
    deg (bigDivisor D small hN hL k hk member hClosed hScale root) = (degree : ℤ) :=
  DegeneratePlacement.divisor_degree _ _ _ _ _ _

/-- **The odd-denominator condition `hBig`.**  Every interior coefficient of the big-side
divisor carries an odd denominator at its own position along the big slot. -/
theorem bigDivisor_interior_mem (hOdd : Odd member.oddMult)
    {root : member.target.V} (hInternal : ¬ IsLeafVertex member.target root)
    (e : Fin Q) (o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e - 1)) :
    ((bigDivisor D small hN hL k hk member hClosed hScale root
          ((D.bigSpec (small.scale k hk) hN hL).interiorVertex e o) : ℤ) : ℚ) *
        (((o.val + 1 : ℕ) : ℚ) / (k : ℚ)) ∈ oddDenominatorSubring := by
  have h := DegeneratePlacement.divisor_interior_mem
    (D.bigSpec (small.scale k hk) hN hL) (degenerateLength D small) member hClosed
    (fit D small hN hL k hk member hScale)
    (fun e' h' ↦ exact D small hN hL k hk member hScale e' h') hOdd hInternal e o
  have hcast : (k : ℚ) = (memberScale member : ℚ) := by rw [hScale]
  rw [hcast]
  exact h


/-! ## 4.  `ForestContractionRank`, named, and reduced to an interface of `Utilities` -/

variable (root : member.target.V)

/-- **What `ForestContractionRank` is a statement about.**  The small-side divisor whose
rank `ForestContractionRank` asks for is the pushforward of the member's own original
pullback fibre along a **single** map from the member's source graph onto the
small subdivision: the placement followed by the contraction.  On a
retained slot that composite is the member's realization on the nose; on a
contracted slot both ends of the re-inserted unit edge go to one small core
vertex, so the composite is the member's realization there too.  So
`ForestContractionRank` says exactly that the member's fibre is a `g^1_4` on the metric
graph the member realizes, rather than a free-standing semicontinuity theorem. -/
theorem pushDivisor_bigDivisor :
    ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root) =
      PendantDivisorTransport.push
        (ExpansionData.vertexMap D (small.scale k hk) hN hL ∘
          DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
            (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale))
        (DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
          (degenerateLength D small) member root) :=
  (PendantDivisorTransport.push_comp
      (G := member.data.sourceGraph) (H := (D.bigSpec (small.scale k hk) hN hL).graph)
      (K := (small.scale k hk).graph)
      (DegeneratePlacement.sourcePoint (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member hClosed (fit D small hN hL k hk member hScale))
      (ExpansionData.vertexMap D (small.scale k hk) hN hL)
      (DegeneratePlacement.fibre (D.bigSpec (small.scale k hk) hN hL)
        (degenerateLength D small) member root)).symm


/-- **Rank one survives the forest contraction**, for the divisor this file produces.
It is stated here so that it can be cited, and so that no consumer can confuse one of
the hypotheses above with it; for the members the endgame uses it is proved by
`CorePencilCoverProducer.forestContractionRank_of_markerFreePencilCover`.

Read the type: it is about `rank` of the **pushforward to the small side** of
`bigDivisor`, and it is not implied by `bigDivisor_effective`,
`bigDivisor_degree` or `bigDivisor_interior_mem`. -/
def ForestContractionRank : Prop :=
  rank (small.scale k hk).graph
      (ExpansionSeriesMoment.pushDivisor D (small.scale k hk) hN hL
        (bigDivisor D small hN hL k hk member hClosed hScale root)) ≥ 1

end Receipts

section Reduction

variable (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)

/-- The pushforward of `Count/ExpansionSeriesMoment.lean` **is**
`Utilities.Subdivision.CoreExpansion`'s own contraction certificate's
pushforward. -/
theorem pushDivisor_eq_pushDiv (Bv : CFDiv (D.bigSpec small hN hL).graph) :
    ExpansionSeriesMoment.pushDivisor D small hN hL Bv =
      (ExpansionData.certificate D small hN hL).pushDiv Bv := rfl

/-- **`ForestContractionRank` reduced to reachability.**  The contraction certificate
is valid (`certificate_valid`), so rank one after the forest contraction follows from
reachability at one representative of every contraction fibre, by a firing script
pulled back from the small side. -/
theorem rank_pushDivisor_of_pushableRepresentatives
    (hCond : D.Conditions small.core)
    (Bv : CFDiv (D.bigSpec small hN hL).graph)
    (hReach : (ExpansionData.certificate D small hN hL).PushableReachabilityAtRepresentatives Bv) :
    rank small.graph (ExpansionSeriesMoment.pushDivisor D small hN hL Bv) ≥ 1 := by
  rw [pushDivisor_eq_pushDiv]
  exact GraphContractionCertificate.rank_ge_one_pushDiv_of_pushableRepresentatives
    (ExpansionData.certificate D small hN hL) (ExpansionData.certificate_valid hCond) hReach

end Reduction

/-! ## 5.  The assembly -/

/-- **Brill--Noether existence from a closed odd member, with `ForestContractionRank` as
the one hypothesis.**  From a `Closed` odd-multiplicity member over `D.bigCore` at the
**degenerate** request, at an internal root, Brill--Noether existence on the requested
subdivision at the odd part `u` of the member's own realization scale.

Everything except `hRank` is proved here or below: the divisor is
`bigDivisor`, a literal pushforward of the member's own pullback fibre;
`hEff` and `hDeg` are `bigDivisor_effective` and `bigDivisor_degree`; `hBig` is
`bigDivisor_interior_mem`; and the descent to the odd part is
`TransportedChipEndgame.bnExists_of_pencil_slotMoment`, reached through
`ExpansionSeriesMoment.bnExists_of_bigDivisor`. -/
theorem bnExists_of_degenerateMember {n p N Q : ℕ}
    (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core)
    (u a : ℕ) (hu : 0 < u) (hk : 0 < 2 ^ a * u)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    (hScale : memberScale member = 2 ^ a * u)
    (root : member.target.V) (hInternal : ¬ IsLeafVertex member.target root)
    (hRank : ForestContractionRank D small hN hL (2 ^ a * u) hk member hClosed hScale root) :
    BNExists (small.scale u hu).graph 1 4 :=
  ExpansionSeriesMoment.bnExists_of_bigDivisor (hN := hN) (hL := hL) small hCond u a hu hk
    (bigDivisor D small hN hL (2 ^ a * u) hk member hClosed hScale root)
    (bigDivisor_effective D small hN hL (2 ^ a * u) hk member hClosed hScale root)
    (bigDivisor_degree D small hN hL (2 ^ a * u) hk member hClosed hScale root)
    hRank
    (fun e o ↦ bigDivisor_interior_mem D small hN hL (2 ^ a * u) hk member hClosed hScale
      hOdd hInternal e o)


/-- **The odd-scale form.**  The same conclusion with the odd part of the
member's own realization scale extracted, in the shape `∃ N, ∃ hN, Odd N ∧ BNExists …`
of the genus-six odd-subdivision witness. -/
theorem exists_odd_scale_bnExists_of_degenerateMember {n p N Q : ℕ}
    (small : Spec n p) (D : ExpansionData n p N Q) (hN : 0 < N)
    (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e)
    (hCond : D.Conditions small.core)
    (member : FibreMember D.bigCore (fun e ↦ (degenerateLength D small e : ℚ)) 4)
    (hClosed : member.Closed) (hOdd : Odd member.oddMult)
    (root : member.target.V) (hInternal : ¬ IsLeafVertex member.target root)
    (hRank : ∀ (u a : ℕ) (hk : 0 < 2 ^ a * u) (hScale : memberScale member = 2 ^ a * u),
      ForestContractionRank D small hN hL (2 ^ a * u) hk member hClosed hScale root) :
    ∃ u : ℕ, ∃ hu : 0 < u, Odd u ∧ BNExists (small.scale u hu).graph 1 4 := by
  obtain ⟨a, u, hOddU, hEq⟩ :=
    Nat.exists_eq_two_pow_mul_odd (memberScale_pos member).ne'
  have hu : 0 < u := by
    obtain ⟨t, ht⟩ := hOddU
    omega
  have hk : 0 < 2 ^ a * u := hEq ▸ memberScale_pos member
  exact ⟨u, hu, hOddU, bnExists_of_degenerateMember small D hN hL hCond u a hu hk member
    hClosed hOdd hEq root hInternal (hRank u a hk hEq)⟩

end DraismaVargas.Count.DegenerateBigDivisor
