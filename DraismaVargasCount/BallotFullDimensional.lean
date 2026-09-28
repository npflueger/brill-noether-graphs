import DraismaVargasCount.BallotGenus
import DraismaVargas.LocalCases.CaterpillarRows

/-!
# The full-dimensional presentation of the ballot-parametrized caterpillar

`BallotDatum` turns the caterpillar gluing datum `caterpillarDatum m` of
`DraismaVargas.LocalCases.CaterpillarDatum` into a family
`BallotDatum.ballotDatum m s`, one for each slope sequence
`s : Slopes (2 * (m + 1))`, proves `ballotDatum_valid` and
`saturated_ballotDatum`, and identifies `caterpillarDatum m` as the zig-zag
member (`ballotDatum_zig`).  This module supplies the rest of
`FullDimensionalSource.FullDimensionalSourcePresentation` for that family:
the honest stable labelling, the `SeedDeterminant.DiagonalPattern`, the
determinant, and the assembly.  Together with
`DraismaVargasCount.BallotStemCensus`, `BallotSpineCensus` and `BallotValency`
it gives the full-dimensional presentation (diagonal pattern, positive
determinant) of every ballot datum, from which the ballot family of the base
count over the caterpillar of loops is built (step 1 of
`DraismaVargasCount/Assembly.lean`).

## What is proved

* §1 -- **a datum-generic row calculus.**  For an arbitrary
  `data : GluingDatum target degree`, two properties of the pruned source,

  - `RowsInFibres data` : consecutive surviving occurrences lie over the same
    target occurrence (stable paths never cross a target fibre), and
  - `FibresInRows data` : surviving occurrences over the same target
    occurrence lie on the same stable path,

  together with a surviving representative `main` over each target
  occurrence, give the row equivalence `occRowEquiv`, the honest labelling
  `rowLabelling`, the diagonal index pattern `rowDiagonalPattern`, and hence
  `rowDet_pos` / `rowDet_ne_zero`.  Nothing here mentions the caterpillar.
  This is the row argument of `LocalCases.CaterpillarRows` with its
  caterpillar input abstracted away.
* §2 -- **the handover for every ballot sequence.**
  `ballotPresentationOfStableData m s` discharges four of the eight fields of
  `FullDimensionalSourcePresentation` for `ballotDatum m s`, uniformly in `m`
  and in `s` (`valid`, `targetConnected`, `targetGenus`, `saturated`), and
  takes the other four as arguments.
  `ballotPresentationOfRowData` replaces two of those four (`labelling`,
  `det_ne_zero`) by the three pruning-census inputs of §1, so the
  obligations for a general `s` are exactly:
  `mainSurvives`, `RowsInFibres`, `FibresInRows`, `trivalent`, `pathEnds`.
* §3 -- **the complete leaf-fibre census, for every ballot sequence.**  Over
  each of the `g` leaf edges of `catTree m` the sheets `0` and
  `cum s (lolli …)` give two distinct source occurrences with the same ordered
  endpoints, so both survive pruning (`bLoopFirst_survives`,
  `bLoopSecond_survives`); every other sheet ends in a source vertex of graph
  degree one and therefore dangles (`bLeafOccurrence_dangles`).  Together they
  are `bLeafOccurrence_isDangling_iff`, which is
  `CaterpillarPruning.leafOccurrence_isDangling_iff` with the zig-zag's
  partner sheet `pairIndex` replaced by the general counter `cum s (lolli ·)`.
  This is the positive-genus anchor the whole census rests on, and it is
  sequence-independent: `vertPred_cum` says the counter label is glued to the
  spine sheet at *every* target vertex.  In particular the `mainSurvives`
  obligation of §2 is discharged over every leaf edge for every `s`
  (`ballot_mainSurvives_leaf`).
* §4 -- **the zig-zag member, completely.**  `zigFullDim m` is an actual
  `FullDimensionalSourcePresentation (ballotDatum m (zig m)) (Fin (6 m + 3))`,
  built through §1 and §2 from the five obligations, each of which is a
  proposition about `ballotDatum m (zig m)` and is proved by rewriting with
  `ballotDatum_zig` and citing the `LocalCases.CaterpillarRows` /
  `LocalCases.CaterpillarValency` theorems.  `zigDiagonalPattern` and
  `zigDet_pos` come with it.

## Scope

* **The five obligations of §2 are proved here only at the zig-zag.**  For a
  general slope sequence `s` this module proves none of
  `mainSurvives` (except over leaf edges, §3), `RowsInFibres`,
  `FibresInRows`, `trivalent`, `pathEnds`.  They
  are the *pruning census* of the general ballot source, and each one is
  genuinely sequence-dependent in the following precise sense.  The
  caterpillar proofs of all five factor through the exact fibre censuses
  `CaterpillarPruning.leafOccurrence_isDangling_iff`,
  `CaterpillarPruning.stemOccurrence_isDangling_iff` and
  `CaterpillarSpine.spineOccurrence_isDangling_iff`, whose statements name the
  single partner sheet `pairIndex` of the zig-zag.  At a general `s` a spine
  edge `h_i` carries a block of `s_i` sheets, not two, so the surviving
  occurrence over `h_i` is one block of size `s_i` and the dangling ones are
  the `m + 2 - s_i` singletons; the *statement* of the census, not merely its
  proof, changes with `s`.  §3 shows the **leaf** layer of that census is
  nevertheless uniform, and proves it.  The stem and spine layers are
  `DraismaVargasCount.BallotStemCensus` and `BallotSpineCensus`, and
  `BallotValency` reads the two stable-row properties and trivalence off the
  three layers together, giving the presentation `BallotValency.ballotFullDim`
  at every `s`.
* **`FullDimensionalSourcePresentation` is not `BallotFamily`.**  No
  `FibreMember`, no `catCore`, no `GeometricFibre`, no `openOddCount` occurs
  below.  `CaterpillarBallot.BallotFamily` is inhabited, at every `m` and every
  positive request, by `BallotCoreIdentification.ballotFamily`, but not
  constructed here.  The presentation is a step towards the ballot members,
  not the members.
* **No genericity hypothesis is used or supplied.**  The count of Vargas,
  Part II (arXiv:2609.09109), `prop-divisors-on-chain`, assumes pairwise
  distinct edge lengths of the metric caterpillar; that hypothesis serves the
  uniqueness half of the ballot classification and does not appear here.  The
  length matrix of §1 is the combinatorial one attached to the labelling.
* **No claim about the number of ballot data, mod 2 or otherwise.**  The
  Catalan number `catalan n` is odd exactly when `n = 2^k - 1`, so the mod-2
  route to an odd count runs only in genus `2, 6, 14, 30, 62, …`; nothing here
  counts anything.
* `zigFullDim` supplies the *presentation*, not the semantic seed.  The entry
  point of the march is `LocalCases.CaterpillarSeed.uniformInitialState`, which
  is stated for `caterpillarDatum m`; transporting it along `ballotDatum_zig`
  is not done here.
-/

namespace DraismaVargas.Count.BallotFullDimensional

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum

/-! ## 1.  A datum-generic row calculus

Two facts about the pruned source of *any* gluing datum make the stable rows
equinumerous with the target occurrences, in the honest sense of an actual
bijection between stable-path classes and occurrences: stable paths do not
leave a target fibre, and a target fibre does not split between stable paths.
Together with one surviving representative per fibre they give the labelling,
the diagonal pattern, and the determinant.  -/

section GenericRows

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **Stable paths do not cross target fibres**: two consecutive surviving
occurrences lie over one and the same target occurrence. -/
def RowsInFibres (data : GluingDatum target degree) : Prop :=
  ∀ first second : NonDanglingEdge data,
    Consecutive data first second → first.1.1.1 = second.1.1.1

/-- **Target fibres do not split between stable paths**: two surviving
occurrences over the same target occurrence lie on the same stable path. -/
def FibresInRows (data : GluingDatum target degree) : Prop :=
  ∀ first second : NonDanglingEdge data,
    first.1.1.1 = second.1.1.1 → first.stablePath = second.stablePath

/-- The target occurrence beneath a stable path. -/
noncomputable def rowOcc (hRows : RowsInFibres data) :
    StablePath data → target.edges :=
  Quot.lift (fun edge : NonDanglingEdge data => edge.1.1.1) hRows

@[simp] theorem rowOcc_stablePath (hRows : RowsInFibres data)
    (edge : NonDanglingEdge data) :
    rowOcc hRows edge.stablePath = edge.1.1.1 := rfl

/-- **The honest row equivalence**: stable-path classes are the target
occurrences, by an actual bijection. -/
noncomputable def occRowEquiv (hRows : RowsInFibres data)
    (hFibres : FibresInRows data) (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence) :
    StablePath data ≃ target.edges where
  toFun := rowOcc hRows
  invFun occurrence := (main occurrence).stablePath
  left_inv := by
    intro path
    induction path using Quot.inductionOn with
    | h edge => exact hFibres _ _ (hmain _)
  right_inv := fun occurrence => hmain occurrence

@[simp] theorem occRowEquiv_apply (hRows : RowsInFibres data)
    (hFibres : FibresInRows data) (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence)
    (edge : NonDanglingEdge data) :
    occRowEquiv hRows hFibres main hmain edge.stablePath = edge.1.1.1 := rfl

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **The honest stable length-matrix labelling** produced by the row
calculus. -/
noncomputable def rowLabelling (targetEdge : coordinate ≃ target.edges)
    (hRows : RowsInFibres data) (hFibres : FibresInRows data)
    (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence) :
    StableLengthMatrixLabelling data coordinate where
  targetEdge := targetEdge
  row := (occRowEquiv hRows hFibres main hmain).trans targetEdge.symm

omit [Fintype coordinate] [DecidableEq coordinate] in
@[simp] theorem rowLabelling_row (targetEdge : coordinate ≃ target.edges)
    (hRows : RowsInFibres data) (hFibres : FibresInRows data)
    (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence)
    (edge : NonDanglingEdge data) :
    (rowLabelling targetEdge hRows hFibres main hmain).row edge.stablePath
      = targetEdge.symm edge.1.1.1 := rfl

omit [Fintype coordinate] in
/-- **The diagonal index pattern.**  Every surviving occurrence displayed by a
row lies over that row's own target column, and the row's chosen
representative shows that no row is empty. -/
theorem rowDiagonalPattern (targetEdge : coordinate ≃ target.edges)
    (hRows : RowsInFibres data) (hFibres : FibresInRows data)
    (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence) :
    DraismaVargas.LocalCases.SeedDeterminant.DiagonalPattern
      (rowLabelling targetEdge hRows hFibres main hmain).presentation where
  liesOver := by
    intro sourceRow edge hMem
    obtain ⟨hSurvives, hRow⟩ :=
      (StableLengthMatrixLabelling.mem_path_iff
        (rowLabelling targetEdge hRows hFibres main hmain) sourceRow edge).mp hMem
    have hRow' : targetEdge.symm edge.1.1 = sourceRow := hRow
    show edge.1.1 = targetEdge sourceRow
    rw [← hRow', Equiv.apply_symm_apply]
  pathNeNil := by
    intro sourceRow hEmpty
    have hRow : (rowLabelling targetEdge hRows hFibres main hmain).row
        (NonDanglingEdge.stablePath (main (targetEdge sourceRow))) = sourceRow := by
      show targetEdge.symm (main (targetEdge sourceRow)).1.1.1 = sourceRow
      rw [hmain, Equiv.symm_apply_apply]
    have hMem : (main (targetEdge sourceRow)).1 ∈
        (rowLabelling targetEdge hRows hFibres main hmain).path sourceRow :=
      (StableLengthMatrixLabelling.mem_path_iff _ _ _).mpr
        ⟨(main (targetEdge sourceRow)).2, hRow⟩
    rw [show (rowLabelling targetEdge hRows hFibres main hmain).path sourceRow
      = [] from hEmpty] at hMem
    exact List.not_mem_nil hMem

theorem rowDet_pos (targetEdge : coordinate ≃ target.edges)
    (hRows : RowsInFibres data) (hFibres : FibresInRows data)
    (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix
      (rowLabelling targetEdge hRows hFibres main hmain).presentation).det :=
  (rowDiagonalPattern targetEdge hRows hFibres main hmain).det_pos

theorem rowDet_ne_zero (targetEdge : coordinate ≃ target.edges)
    (hRows : RowsInFibres data) (hFibres : FibresInRows data)
    (main : target.edges → NonDanglingEdge data)
    (hmain : ∀ occurrence, (main occurrence).1.1.1 = occurrence) :
    (GluingDatum.LengthMatrixPresentation.matrix
      (rowLabelling targetEdge hRows hFibres main hmain).presentation).det ≠ 0 :=
  (rowDiagonalPattern targetEdge hRows hFibres main hmain).det_ne_zero

end GenericRows

/-! ## 2.  The handover, for every ballot sequence

`CaterpillarStable.presentationOfStableData` is the caterpillar version of
the first `def` below: four fields free, four obligations explicit.  The second
`def` runs the four obligations through §1, so that what a general slope
sequence needs beyond it is exactly the pruning census of its source. -/

/-- **Four of the eight fields of the seed presentation are discharged for
every slope sequence.**  The four supplied are `valid`
(`BallotDatum.ballotDatum_valid`, uniform in `g` and in `s`), `targetConnected`
and `targetGenus` (properties of `catTree m` alone), and `saturated`
(`BallotDatum.saturated_ballotDatum`, the Euler count `3g - 3 = 2g + 2d - 5`).
The four explicit arguments are exactly what the presentation needs beyond
these for a general `s`. -/
noncomputable def ballotPresentationOfStableData (m : ℕ) (s : Slopes (2 * (m + 1)))
    (labelling : StableLengthMatrixLabelling (ballotDatum m s) (Fin (6 * m + 3)))
    (det_ne_zero : (GluingDatum.LengthMatrixPresentation.matrix
      labelling.presentation).det ≠ 0)
    (trivalent : ∀ vertex : (ballotDatum m s).SourceVertex,
      nonDanglingValency (ballotDatum m s) vertex ≤ 3)
    (pathEnds : HasPathEnds (ballotDatum m s)) :
    FullDimensionalSourcePresentation (ballotDatum m s) (Fin (6 * m + 3)) where
  valid := ballotDatum_valid m s
  targetConnected := catTree_connected m
  targetGenus := catTree_genus m
  saturated := saturated_ballotDatum m s
  labelling := labelling
  det_ne_zero := det_ne_zero
  trivalent := trivalent
  pathEnds := pathEnds

/-- The spine-sheet occurrence over a target occurrence: the representative
that §1 needs, named uniformly in `m` and `s`. -/
noncomputable def bMain (m : ℕ) (s : Slopes (2 * (m + 1)))
    (occurrence : (catTree m).edges) : (ballotDatum m s).SourceEdge :=
  (ballotDatum m s).sourceEdge occurrence 0

@[simp] theorem bMain_target (m : ℕ) (s : Slopes (2 * (m + 1)))
    (occurrence : (catTree m).edges) : (bMain m s occurrence).1.1 = occurrence := rfl

/-- **The obligation list of the presentation for a general ballot
sequence.**  Given the pruning census of the source of `ballotDatum m s` --
survival of the spine-sheet occurrence over every target occurrence, the two
stable-row properties of §1, trivalence and the path-end condition -- the
honest labelling, its diagonal pattern and its nonsingular determinant are
supplied here, and the full-dimensional presentation follows. -/
noncomputable def ballotPresentationOfRowData (m : ℕ) (s : Slopes (2 * (m + 1)))
    (mainSurvives : ∀ occurrence : (catTree m).edges,
      ¬ IsDangling (ballotDatum m s) (bMain m s occurrence))
    (hRows : RowsInFibres (ballotDatum m s))
    (hFibres : FibresInRows (ballotDatum m s))
    (trivalent : ∀ vertex : (ballotDatum m s).SourceVertex,
      nonDanglingValency (ballotDatum m s) vertex ≤ 3)
    (pathEnds : HasPathEnds (ballotDatum m s)) :
    FullDimensionalSourcePresentation (ballotDatum m s) (Fin (6 * m + 3)) :=
  ballotPresentationOfStableData m s
    (rowLabelling (catEdgeEquiv m) hRows hFibres
      (fun occurrence => ⟨bMain m s occurrence, mainSurvives occurrence⟩)
      (fun _ => rfl))
    (rowDet_ne_zero (catEdgeEquiv m) hRows hFibres _ _) trivalent pathEnds


/-! ## 3.  The loop anchors, for every ballot sequence

The `g` loops of the source sit over the `g` leaf edges of the target, and they
are there for *every* slope sequence: the partition over a leaf edge is
discrete, while at both of its endpoints the lollipop's counter label
`cum s (lolli ·)` is glued to the spine sheet `0`.  So the two flags are
distinct occurrences with the same ordered endpoints, and a dangling cut needs
its distinguished occurrence to be the unique crossing one.

This is the only layer of the pruning census that is uniform in `s`: it does
not mention a spine block, whose size `s_i` is exactly what varies. -/

section LoopAnchors

variable {m : ℕ}

/-- **The counter label of a lollipop is glued to the spine sheet at every
target vertex.**  At a junction this is `Slopes.vertMem_of_pairMem`; elsewhere
the block is the bridge pair `{0, cum}` itself. -/
theorem vertPred_cum (s : Slopes (2 * (m + 1))) (a : ℕ) :
    VertPred m s a (s.cum (lolli a)) := by
  unfold VertPred
  by_cases h : a % 3 = 2
  · rw [if_pos h]
    exact Slopes.vertMem_of_pairMem s (Or.inr rfl)
  · rw [if_neg h]
    exact Or.inr rfl

/-- The sheet carrying the counter label of the lollipop containing `a`. -/
def cumSheet (m : ℕ) (s : Slopes (2 * (m + 1))) (a : ℕ) : Fin (m + 2) :=
  ⟨s.cum (lolli a), by have := Slopes.cum_le s rfl (lolli a); omega⟩

@[simp] theorem cumSheet_val (s : Slopes (2 * (m + 1))) (a : ℕ) :
    (cumSheet m s a).val = s.cum (lolli a) := rfl

theorem cumSheet_ne_zero (s : Slopes (2 * (m + 1))) (a : ℕ) :
    cumSheet m s a ≠ 0 := by
  intro h
  have hval := congrArg Fin.val h
  rw [cumSheet_val] at hval
  have hpos := Slopes.one_le_cum s (lolli a)
  simp only [Fin.val_zero] at hval
  omega

/-- **The counter sheet meets the spine sheet above every target vertex.** -/
theorem sourceEndpoint_cumSheet (s : Slopes (2 * (m + 1))) (v : (catTree m).V) :
    (ballotDatum m s).sourceEndpoint v (cumSheet m s v.val)
      = (ballotDatum m s).sourceEndpoint v 0 := by
  refine (ballotDatum m s).sourceEndpoint_congr v ?_
  show (catStar m (VertPred m s v.val)).Rel (cumSheet m s v.val) 0
  rw [catStar_rel_iff _ (vertPred_zero s _)]
  exact Or.inl ⟨vertPred_cum s v.val, vertPred_zero s _⟩

/-- Over a leaf edge the occurrence partition is discrete for every slope
sequence: its block is the spine sheet alone. -/
theorem ballotEdgePart_leaf (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    (ballotDatum m s).edgePartition (occ m i) = SheetPartition.discrete (m + 2) := by
  rw [ballotDatum_edgePart_occ]
  exact catStar_eq_discrete _ (edgePred_leaf s hLeaf)

/-- A leaf edge and its parent endpoint belong to the same lollipop. -/
theorem lolli_parentIndex_leaf {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    lolli (parentIndex (i.val + 1)) = lolli (i.val + 1) := by
  have hi := i.isLt
  unfold CaterpillarPruning.IsLeafEdge at hLeaf
  unfold lolli parentIndex
  rcases hLeaf with h | h
  · rw [if_neg (by omega)]; omega
  · rw [if_neg (by omega)]; omega

/-- The spine-sheet flag over a leaf edge. -/
noncomputable def bLoopFirst (m : ℕ) (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) : (ballotDatum m s).SourceEdge :=
  (ballotDatum m s).sourceEdge (occ m i) 0

/-- The counter-sheet flag over a leaf edge. -/
noncomputable def bLoopSecond (m : ℕ) (s : Slopes (2 * (m + 1)))
    (i : Fin (6 * m + 3)) : (ballotDatum m s).SourceEdge :=
  (ballotDatum m s).sourceEdge (occ m i) (cumSheet m s (i.val + 1))

theorem bLoopFirst_ne_bLoopSecond (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    bLoopFirst m s i ≠ bLoopSecond m s i := by
  intro hEq
  have hSheet : ((ballotDatum m s).edgePartition (occ m i)).repr 0
      = ((ballotDatum m s).edgePartition (occ m i)).repr (cumSheet m s (i.val + 1)) :=
    congrArg (fun edge : (ballotDatum m s).SourceEdge => edge.1.2) hEq
  rw [ballotEdgePart_leaf s hLeaf] at hSheet
  exact cumSheet_ne_zero s (i.val + 1) hSheet.symm

/-- **The two flags over a leaf edge have the same ordered endpoints.** -/
theorem sourceEnds_bLoopSecond (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    (ballotDatum m s).sourceEnds (bLoopSecond m s i)
      = (ballotDatum m s).sourceEnds (bLoopFirst m s i) := by
  unfold bLoopSecond bLoopFirst
  rw [sourceEnds_sourceEdge, sourceEnds_sourceEdge]
  refine Prod.ext ?_ ?_
  · show (ballotDatum m s).sourceEndpoint (catParent m i) (cumSheet m s (i.val + 1))
      = (ballotDatum m s).sourceEndpoint (catParent m i) 0
    have hlolli : cumSheet m s (catParent m i).val = cumSheet m s (i.val + 1) := by
      apply Fin.ext
      rw [cumSheet_val, cumSheet_val, catParent_val, lolli_parentIndex_leaf hLeaf]
    rw [← hlolli]
    exact sourceEndpoint_cumSheet s (catParent m i)
  · show (ballotDatum m s).sourceEndpoint i.succ (cumSheet m s (i.val + 1))
      = (ballotDatum m s).sourceEndpoint i.succ 0
    exact sourceEndpoint_cumSheet s i.succ

/-- **Both flags of every ballot loop survive pruning**, for every slope
sequence. -/
theorem bLoopFirst_survives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    ¬ IsDangling (ballotDatum m s) (bLoopFirst m s i) :=
  CaterpillarPruning.not_isDangling_of_parallel (ballotDatum m s)
    (bLoopFirst_ne_bLoopSecond s hLeaf) (sourceEnds_bLoopSecond s hLeaf)

theorem bLoopSecond_survives (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    ¬ IsDangling (ballotDatum m s) (bLoopSecond m s i) :=
  CaterpillarPruning.not_isDangling_of_parallel (ballotDatum m s)
    (bLoopFirst_ne_bLoopSecond s hLeaf).symm (sourceEnds_bLoopSecond s hLeaf).symm

/-- **The `mainSurvives` obligation of §2, discharged over every leaf edge for
every slope sequence.**  The rest of that obligation, over the spine and stem
occurrences, where the block has `s_i` sheets and the argument does depend on
the sequence, is `BallotSpineCensus.ballot_mainSurvives`. -/
theorem ballot_mainSurvives_leaf (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) :
    ¬ IsDangling (ballotDatum m s) (bMain m s (occ m i)) :=
  bLoopFirst_survives s hLeaf

/-! ### The complete leaf fibre census, for every ballot sequence

Away from the two flags the fibre over a leaf edge consists of `m` singleton
sheets, and each of them ends in a source vertex of graph degree one: the leaf
end of the target carries no other occurrence, the occurrence partition there
is discrete and the vertex block is a singleton.  So the census over a leaf
edge is complete and uniform in `s`: exactly two survivors, exactly `m`
dangling occurrences. -/

theorem catStar_repr_of_not (P : ℕ → Prop) [DecidablePred P] {σ : Fin (m + 2)}
    (hσ : ¬ P σ.val) : (catStar m P).repr σ = σ :=
  SheetPartition.sheetStar_repr_of_not P hσ

/-- The block at the leaf end of a leaf edge is the bridge pair `{0, cum}`. -/
theorem vertPred_leafChild_iff (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) (k : ℕ) :
    VertPred m s (i.val + 1) k ↔ (k = 0 ∨ k = s.cum (lolli (i.val + 1))) := by
  have hi := i.isLt
  have hmod : (i.val + 1) % 3 ≠ 2 := by
    rcases hLeaf with h | h <;> omega
  rw [vertPred_pair s hmod]
  exact Iff.rfl

/-- Away from the two flags, the source vertex above the leaf end has graph
degree one: its target vertex carries only the leaf occurrence, the occurrence
partition there is discrete, and the vertex block is a singleton. -/
theorem bLeaf_vertex_degree_one (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) (v : (catTree m).V)
    (hv : v.val = i.val + 1) (σ : Fin (m + 2))
    (h0 : σ.val ≠ 0) (hcum : σ.val ≠ s.cum (lolli (i.val + 1))) :
    vertex_degree (ballotDatum m s).sourceGraph
        ((ballotDatum m s).sourceEndpoint v σ) = 1 := by
  have hi := i.isLt
  have hnot : ¬ VertPred m s v.val σ.val := by
    rw [hv, vertPred_leafChild_iff s hLeaf]
    rintro (h | h)
    · exact h0 h
    · exact hcum h
  have hs : ((ballotDatum m s).sourceEndpoint v σ).1.2 = σ :=
    catStar_repr_of_not (VertPred m s v.val) hnot
  have hInc : incidentIndices m v = {i} := by
    ext j
    have hj := j.isLt
    simp only [mem_incidentIndices, Finset.mem_singleton, Fin.ext_iff,
      parentIndex_eq_iff, hv]
    rcases hLeaf with h | h <;> omega
  have hcard : ((ballotDatum m s).vertexPartition v).blockCard σ = 1 :=
    catStar_blockCard_of_not (VertPred m s v.val) (vertPred_zero s _) hnot
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
    card_incidentSourceEdge_eq_sum_blockCountWithin,
    show ((ballotDatum m s).sourceEndpoint v σ).1.1 = v from rfl, hs,
    sum_incidentEdges_one m v hInc
      (fun e => ((ballotDatum m s).edgePartition e).blockCountWithin
        ((ballotDatum m s).vertexPartition v) σ),
    ballotEdgePart_leaf s hLeaf, blockCountWithin_discrete, hcard]
  norm_num

/-- **Every other sheet over a leaf edge dangles.** -/
theorem bLeafOccurrence_dangles (s : Slopes (2 * (m + 1))) {i : Fin (6 * m + 3)}
    (hLeaf : CaterpillarPruning.IsLeafEdge m i) (σ : Fin (m + 2))
    (h0 : σ.val ≠ 0) (hcum : σ.val ≠ s.cum (lolli (i.val + 1))) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ) := by
  refine isDangling_of_sourceEnds_snd_degree_eq_one (ballotDatum m s)
    (ballotDatum_connected m s) _ ?_
  rw [sourceEnds_sourceEdge]
  exact bLeaf_vertex_degree_one s hLeaf _ rfl σ h0 hcum

/-- **The exact leaf-fibre occurrence census, for every slope sequence.**  The
two loop flags -- the spine sheet and the lollipop's counter sheet -- survive
pruning, and every other singleton sheet occurrence dangles.  This is
`CaterpillarPruning.leafOccurrence_isDangling_iff` with the zig-zag's partner
sheet `pairIndex` replaced by the general counter `cum s (lolli ·)`. -/
theorem bLeafOccurrence_isDangling_iff (s : Slopes (2 * (m + 1)))
    {i : Fin (6 * m + 3)} (hLeaf : CaterpillarPruning.IsLeafEdge m i)
    (σ : Fin (m + 2)) :
    IsDangling (ballotDatum m s) ((ballotDatum m s).sourceEdge (occ m i) σ)
      ↔ (σ.val ≠ 0 ∧ σ.val ≠ s.cum (lolli (i.val + 1))) := by
  constructor
  · intro hDangling
    refine ⟨?_, ?_⟩
    · intro h0
      have hσ : σ = 0 := Fin.ext (by simpa using h0)
      subst hσ
      exact bLoopFirst_survives s hLeaf hDangling
    · intro hcum
      have hσ : σ = cumSheet m s (i.val + 1) := Fin.ext (by rw [cumSheet_val]; exact hcum)
      subst hσ
      exact bLoopSecond_survives s hLeaf hDangling
  · rintro ⟨h0, hcum⟩
    exact bLeafOccurrence_dangles s hLeaf σ h0 hcum

end LoopAnchors

/-! ## 4.  The zig-zag member, completely

Each of the five obligations of §2 is a *proposition* about
`ballotDatum m (zig m)`, so `ballotDatum_zig` discharges it by rewriting: no
term of a datum-dependent type is transported, and the caterpillar theorems
of `LocalCases` apply verbatim on the other side of the rewrite. -/

theorem zig_mainSurvives (m : ℕ) (occurrence : (catTree m).edges) :
    ¬ IsDangling (ballotDatum m (zig m)) (bMain m (zig m) occurrence) := by
  obtain ⟨i, rfl⟩ := occ_surj m occurrence
  show ¬ IsDangling (ballotDatum m (zig m))
    ((ballotDatum m (zig m)).sourceEdge (occ m i) 0)
  rw [ballotDatum_zig]
  exact CaterpillarRows.main_survives m i

theorem zig_rowsInFibres (m : ℕ) : RowsInFibres (ballotDatum m (zig m)) := by
  rw [ballotDatum_zig]
  intro first second h
  exact CaterpillarValency.target_eq_of_consecutive first second h

theorem zig_fibresInRows (m : ℕ) : FibresInRows (ballotDatum m (zig m)) := by
  rw [ballotDatum_zig]
  intro first second h
  rw [CaterpillarRows.edge_stablePath_eq_main m first,
    CaterpillarRows.edge_stablePath_eq_main m second, h]

theorem zig_trivalent (m : ℕ) :
    ∀ vertex : (ballotDatum m (zig m)).SourceVertex,
      nonDanglingValency (ballotDatum m (zig m)) vertex ≤ 3 := by
  rw [ballotDatum_zig]
  exact CaterpillarValency.nonDanglingValency_le_three m

theorem zig_pathEnds (m : ℕ) : HasPathEnds (ballotDatum m (zig m)) := by
  rw [ballotDatum_zig]
  exact CaterpillarRows.hasPathEnds m

/-- **The honest stable length-matrix labelling of the zig-zag ballot
datum**, over the coordinate type `Fin (3g - 3)`. -/
noncomputable def zigLabelling (m : ℕ) :
    StableLengthMatrixLabelling (ballotDatum m (zig m)) (Fin (6 * m + 3)) :=
  rowLabelling (catEdgeEquiv m) (zig_rowsInFibres m) (zig_fibresInRows m)
    (fun occurrence => ⟨bMain m (zig m) occurrence, zig_mainSurvives m occurrence⟩)
    (fun _ => rfl)

/-- **The diagonal index pattern of the zig-zag ballot datum.** -/
theorem zigDiagonalPattern (m : ℕ) :
    DraismaVargas.LocalCases.SeedDeterminant.DiagonalPattern (zigLabelling m).presentation :=
  rowDiagonalPattern (catEdgeEquiv m) (zig_rowsInFibres m) (zig_fibresInRows m) _ _

theorem zigDet_pos (m : ℕ) :
    0 < (GluingDatum.LengthMatrixPresentation.matrix (zigLabelling m).presentation).det :=
  (zigDiagonalPattern m).det_pos

theorem zigDet_ne_zero (m : ℕ) :
    (GluingDatum.LengthMatrixPresentation.matrix (zigLabelling m).presentation).det ≠ 0 :=
  (zigDiagonalPattern m).det_ne_zero

/-- **The full-dimensional presentation at the zig-zag ballot sequence.**  The
ballot-parametrized datum at `(2,1,2,1,…,2)` carries a full-dimensional source
presentation over
`Fin (3g - 3)`, for every even genus `g = 2m + 2`. -/
noncomputable def zigFullDim (m : ℕ) :
    FullDimensionalSourcePresentation (ballotDatum m (zig m)) (Fin (6 * m + 3)) :=
  ballotPresentationOfRowData m (zig m) (zig_mainSurvives m) (zig_rowsInFibres m)
    (zig_fibresInRows m) (zig_trivalent m) (zig_pathEnds m)

@[simp] theorem zigFullDim_labelling (m : ℕ) :
    (zigFullDim m).labelling = zigLabelling m := rfl

/-! ## 5.  Non-vacuity

The family is really populated: at genus six there are five slope sequences,
and `Slopes.six = [2,3,4,3,2]` is one that is not the zig-zag, with spine
blocks of four sheets.  The leaf census of §3 applies to it verbatim. -/

/-- Genus six, degree four: the leaf-fibre census holds for the
rise-then-fall sequence, which is not the zig-zag. -/
example (i : Fin (6 * 2 + 3)) (hLeaf : CaterpillarPruning.IsLeafEdge 2 i)
    (σ : Fin (2 + 2)) :
    IsDangling (ballotDatum 2 Slopes.six)
        ((ballotDatum 2 Slopes.six).sourceEdge (occ 2 i) σ)
      ↔ (σ.val ≠ 0 ∧ σ.val ≠ Slopes.six.cum (lolli (i.val + 1))) :=
  bLeafOccurrence_isDangling_iff Slopes.six hLeaf σ

/-- …and the loop anchors hold for every one of the five sequences. -/
example (s : Slopes 6) (i : Fin (6 * 2 + 3))
    (hLeaf : CaterpillarPruning.IsLeafEdge 2 i) :
    ¬ IsDangling (ballotDatum 2 s) (bMain 2 s (occ 2 i)) :=
  ballot_mainSurvives_leaf s hLeaf

/-- The zig-zag member carries an actual full-dimensional presentation at
genus six, over the fifteen coordinates `3g - 3`. -/
noncomputable example :
    FullDimensionalSourcePresentation (ballotDatum 2 (zig 2)) (Fin (6 * 2 + 3)) :=
  zigFullDim 2

/-- **Consistency.**  The caterpillar datum `caterpillarDatum m` receives the
zig-zag member's presentation, read through `ballotDatum_zig`. -/
noncomputable example (m : ℕ) :
    FullDimensionalSourcePresentation (caterpillarDatum m) (Fin (6 * m + 3)) := by
  rw [← ballotDatum_zig m]
  exact zigFullDim m

end DraismaVargas.Count.BallotFullDimensional
