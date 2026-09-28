import DraismaVargasCount.SegmentWalls
import DraismaVargas.Infrastructure.IteratedContraction
import DraismaVargas.Infrastructure.PartitionNormalization

/-!
# The star of a codimension-one limit, as a quotient

**Scope.** The frame/regrowth infrastructure here is shared, but this file's
`WallStar.Star` uses strict target orientations and a bare unlabelled limit
relation. The labelled metric star used by the count is `GeometricStar.Star`;
it preserves the actual inherited branch and row labels and derives target
metric preservation. The two stars' cardinalities are not identified. The
statements below about the star concern the strict star `WallStar.Star`.

**Source.**  Vargas, Part II (arXiv:2609.09109): the multiset convention
`re:multiset-specializing`, the example `ex-multiset-star` and the balancing
condition `prop-signed-mult`.  Built on `Count.Fibre` (fibre members, the fibre
quotient and its finiteness), `Count.SegmentWalls` (the wall parameters of a
segment) and `Count.Transport` (invariance of the multiplicity under
isomorphism).

## Namespaces

Sections 1--3 add declarations to `DraismaVargas.Count.SegmentWalls`, because
they are dot-notation API on that file's `Frame` and `FrameIso`; nothing there
is changed.  Everything from `Regrowth` on lives in
`DraismaVargas.Count.WallStar`, so that the name `Star` is not introduced into a
namespace existing files already `open`.

## Two remarks on the definition

* **A frame isomorphism cannot move a coordinate.**  Any `FrameIso k l` carries
  the coordinate `col` of `k` to a coordinate of `l` determined by the *pair*
  `(k, l)` alone (`FrameIso.column_eq`), because two coordinates that agree as
  functions of the request are equal rows of `A⁻¹`
  (`Frame.col_eq_of_coordsAt_eq`).  In particular an automorphism of a frame
  over the core is the identity on the target -- on occurrences
  (`FrameIso.targetEdge_self`) and on vertices (`FrameIso.targetVertex_self`).
  So the "isomorphisms of `φ` that fix `column`" by which a star is a quotient
  are *the whole of* `FrameIso`, and `column_eq_of_frameIso` shows the
  condition is automatic.  It also means that in the **labelled** fibre no
  automorphism of a full-dimensional `φ` over the core can cover a
  non-identity automorphism of the base tree: the induced column permutation
  would give `A⁻¹` two equal rows.
* **The face identification `ε` must be a property, not data.**  Suppose a star
  member carried `spec : contract φ column ≅ w.limit` as a field, and the star
  were the quotient by isomorphisms "commuting with `ε`".  With `ε` as data the
  star of a type `φ` with one contractible column is a torsor under
  `Aut(w.limit)` modulo the
  image of `Aut(φ)`, so one incident facet is counted `|Aut(w.limit)| / |image|`
  times and `Σ_{star} signedMult = 0` fails as soon as the limit has an
  automorphism that does not lift.  Here `SameLimit` is `Nonempty (DatumIso …)`,
  a `Prop`, and the multiset phenomenon of `ex-multiset-star` is carried by the
  *labelling* instead: the two branches `ϑ₃ₐ`, `ϑ₃♭` of the example differ by a
  transposition of two core slots, hence are two distinct `FrameIso` classes of
  the labelled fibre, exactly as `re:multiset-specializing` asks.

## What is proved

* **Rigidity** (§1): `Frame.col_eq_of_coordsAt_eq`, `FrameIso.column`,
  `FrameIso.column_eq`, `FrameIso.column_self`, `FrameIso.targetEdge_self`,
  `FrameIso.targetVertex_self`, and `FrameIso.refl`/`symm`/`trans`.
* **Specialization** (§2): `Frame.DegenerateAt k y col` -- the coordinate `col`
  vanishes at `y` and every other coordinate is positive -- with uniqueness of
  the column (`Frame.DegenerateAt.column_unique`), transport along a frame
  isomorphism (`Frame.DegenerateAt.map`), the two sides of the wall
  (`Frame.DegenerateAt.openAt_add_push`, `…not_openAt_sub_push`: the frame is a
  genuinely open member one unit along `Frame.push` and has the coordinate `-1`
  one unit the other way), and the bridge from the segment calculus of
  `Count.SegmentWalls`, `Frame.degenerateAt_of_isWallParam`.
* **The limit** (§3): `Frame.edgeOf`, `Frame.numEdges_edgeOf` (a
  full-dimensional target is a tree, so `num_edges = 1` at every coordinate),
  `Frame.limitTarget` and `Frame.limit`, the contraction
  (`GluingContraction.contractDatumAt`, the limit gluing datum of Draisma--Vargas
  Part I, `def-limit-gluing`) at the vanishing coordinate.
* **The star** (§4): `Regrowth` (frame, column, proof of degeneracy),
  `Regrowth.SameLimit` (an equivalence relation, from `DatumIso`'s own
  `refl`/`symm`/`trans`), `StarMember`, the setoid by `FrameIso` of the frames,
  `Star`, `Star.toFibre` and its injectivity, hence `Finite (Star w)` and
  `Fintype (Star w)` **from the fibre's own finiteness**, and
  `Star.instNonempty`.
* **Membership is specialization** (§5, §10): `SpecializesTo`,
  `specializesTo_iff_sameLimit`, `specializesTo_of_starMember`,
  `specializesTo_map` (specialization is a property of the class),
  `Star.closed` and `Star.not_open` (every star class is in the
  codimension-one stratum of the fibre), `isStarClass_iff` (a class of the
  fibre at the wall request is a star class exactly when its regrowth
  specializes) and `Star.equivSubtype`, the canonical bijection of `Star w`
  with the subtype of the labelled fibre cut out by specialization.
* **Contraction is functorial** (§8, §9, §10): `contractDatumIso` -- a
  `DatumIso` carrying one target occurrence to another induces a `DatumIso` of
  the two contracted data -- and `limitTransports`, its consequence that the
  limit only depends on the `FrameIso` class of the frame.  The sheet algebra
  is §8: `SheetPartition.join` is natural only *up to blocks*
  (`sameBlocks_join_relabel`), because the representative map of a join is the
  least element of each class and no permutation commutes with that choice, so
  the merged vertex needs the repair permutation `mergePerm` built from
  `Infrastructure.PartitionNormalization`.  The input that makes the two
  endpoint permutations agree modulo the join is exactly `DatumIso`'s
  compatibility fields at the contracted occurrence
  (`joinRel_vertexPerm`, `joinRel_vertexPerm_symm`).
* **Non-vacuity** (§7): `catRegrowth`, the caterpillar-of-loops frame with one
  coordinate driven to zero, for every even genus `g = 2m + 2`; its star is
  nonempty and finite.

## What is not proved here (every hypothesis, explicitly)

* **Nothing here proves `Σ_{m ∈ Star w} signedMult m = 0`** (the balancing
  condition of Part II, `prop-signed-mult`), and nothing evaluates a star.
  `Star w` is *defined* and shown finite; which members it has for a given `w`
  (star exhaustion) is not addressed here.
* **A weight `copies / |Aut φ|` is neither proved nor assumed here.**  In this
  formulation such a weight would be a *theorem about orbit counting* --
  `Star w` is the set of `FrameIso` classes of regrowths with the given limit,
  and for a fixed frame the group acting is `Aut(frame)`, which by
  `FrameIso.targetEdge_self` is a group of pure sheet relabellings.  No orbit
  count is carried out in this file; no declaration below mentions `copies`, an
  orbit, or a weight.
* **The labelled star does not quotient by tree automorphisms.**
  `FrameIso.targetEdge_self` shows that over a *labelled* core no automorphism
  of a full-dimensional frame can cover a non-identity tree automorphism, so a
  symmetry of the target tree cannot identify two members of the labelled star.
  An unlabelled star, quotiented by tree automorphisms, is a different object;
  this file makes no claim about it.
* **`Regrowth` does not require the request to be nondegenerate.**
  `Nondegenerate y` (§11) is the Part II condition that only the target edge
  collapses.  `admissibleColumn_of_degenerateAt` shows that under it the
  vanishing coordinate is an *admissible column* in the sense of
  `LocalCases.InteriorProgress.AdmissibleColumn`, which is what Part I's ten-way
  interior classification consumes.
* **The non-vacuity witness of §7 is not a nondegenerate limit.**  Its member,
  the caterpillar member `Count.FibreCaterpillar.caterpillarMember`, has a
  diagonal length matrix, and `catFrame_not_degenerateAt_of_pos` proves that a
  diagonal frame has **no** degeneration at a request with all slots positive.
  So `not_nondegenerate_catWallRequest`: the witness is a request-boundary
  wall, not a Part II codimension-one limit.  A nondegenerate witness needs a
  full-dimensional member with a non-diagonal length matrix, which this file
  does not construct.
  **Remark.**  `catRegrowth m j` at a *non-loop* slot `j`
  (`¬ IsLeafEdge m j`, so `catCore.tail j ≠ catCore.head j`) degenerates a
  genuine core edge, not merely a cover coordinate — the shape of
  `FacetMachine.SharedContractionSlot` and `FacetMachine.FacetDatum` — so it
  reads as a **type-change facet regrowth** rather than an ordinary in-cone
  one.  Nothing in this file or in `FacetMachine` states or proves that
  connection as a theorem; it is an observation about the shapes of the two
  constructions.
* **Validity of the limit is not claimed.**  `Frame.limit` is
  `GluingContraction.contractDatumAt`, a gluing datum; it is *not* shown to be
  `Valid`, which needs `ContractionRamification.ContractionForestAt` and is the
  Draisma--Vargas forest input (`Infrastructure.GluingContraction`'s own
  docstring records that the local Riemann--Hurwitz inequality at the merged
  vertex is not proved there).  No statement in this file needs it.
* **No length matrix of the limit is built.**  The rectangular presentation of
  the codimension-one limit -- p rows, p-1 columns -- and the identification of
  its columns with the surviving columns of a star member, which
  `prop-signed-mult`'s determinant identity runs on, need the member-to-limit
  correspondence of stable rows, which is not built here.  In particular
  `AgreeOffColumn` between two star members is **not** established here.
* **An alternative that does not work.**  Identifying two
  regrowths when their *degenerate members* are isomorphic over the core
  (`IsoOverCore` of `k.member y` and `l.member y`) is strictly finer than
  `SameLimit`: a degenerate member remembers which target occurrence collapsed,
  so that relation makes every star a singleton and `Σ_{star} signedMult = 0`
  false.  The quotient has to be taken after contracting, which is why
  `Frame.limit` is built at all.

## Use

The frame, degeneration, limit and regrowth API of this file is shared
infrastructure for the wall-crossing arguments of the count; in particular
`Frame.degenerateAt_of_isWallParam` is how a wall parameter of
`Count.SegmentWalls` produces a `Regrowth`, and `Nondegenerate` and `Regrowth`
are the inputs of `GeometricStar.Star`.  `Star.equivSubtype` identifies the
strict star with a subtype of the labelled fibre.
-/

namespace DraismaVargas.Count.SegmentWalls

open DraismaVargas.Infrastructure
open DraismaVargas.Count.Transport (DatumIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {degree : ℕ}

/-! ## 1. Rigidity -/

theorem Frame.col_eq_of_coordsAt_eq (k : Frame core degree) {c c' : Fin p}
    (h : ∀ y : Fin p → ℚ, k.coordsAt y c = k.coordsAt y c') : c = c' := by
  classical
  have hrow : ∀ r : Fin p, k.matrix⁻¹ c r = k.matrix⁻¹ c' r := by
    intro r
    have hy := h (fun s ↦ if s = k.slot r then (1 : ℚ) else 0)
    rw [Frame.coordsAt_apply, Frame.coordsAt_apply] at hy
    have hsum : ∀ d : Fin p,
        (∑ row, k.matrix⁻¹ d row * (if k.slot row = k.slot r then (1 : ℚ) else 0)) =
          k.matrix⁻¹ d r := by
      intro d
      rw [Finset.sum_eq_single r]
      · simp
      · intro b _ hb
        have : k.slot b ≠ k.slot r := fun hcon ↦ hb (k.slot.injective hcon)
        simp [this]
      · intro hcon
        exact absurd (Finset.mem_univ r) hcon
    rw [hsum c, hsum c'] at hy
    exact hy
  by_contra hne
  have hone : (1 : Matrix (Fin p) (Fin p) ℚ) c c = (1 : Matrix (Fin p) (Fin p) ℚ) c' c := by
    rw [← Matrix.nonsing_inv_mul _ k.isUnit_det]
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun r _ ↦ by rw [hrow r]
  rw [Matrix.one_apply_eq, Matrix.one_apply_ne (fun hcon ↦ hne hcon.symm)] at hone
  exact one_ne_zero hone

/-- The permutation of coordinates induced by an isomorphism of frames. -/
def FrameIso.column {k l : Frame core degree} (fi : FrameIso k l) : Fin p ≃ Fin p :=
  k.fullDim.labelling.targetEdge.trans
    (fi.datum.targetEdge.trans l.fullDim.labelling.targetEdge.symm)

theorem FrameIso.coordsAt_column {k l : Frame core degree} (fi : FrameIso k l)
    (y : Fin p → ℚ) (col : Fin p) :
    l.coordsAt y (fi.column col) = k.coordsAt y col :=
  Frame.coordsAt_column k l fi.datum fi.overCore_row y col

theorem FrameIso.column_eq {k l : Frame core degree} (fi gi : FrameIso k l) :
    fi.column = gi.column := by
  refine Equiv.ext fun col ↦ ?_
  exact l.col_eq_of_coordsAt_eq
    (fun y ↦ (fi.coordsAt_column y col).trans (gi.coordsAt_column y col).symm)

theorem FrameIso.column_self {k : Frame core degree} (fi : FrameIso k k) (col : Fin p) :
    fi.column col = col :=
  k.col_eq_of_coordsAt_eq (fun y ↦ fi.coordsAt_column y col)

theorem FrameIso.targetEdge_self {k : Frame core degree} (fi : FrameIso k k)
    (e : k.target.edges) : fi.datum.targetEdge e = e := by
  have h := fi.column_self (k.fullDim.labelling.targetEdge.symm e)
  simp only [FrameIso.column, Equiv.trans_apply, Equiv.apply_symm_apply] at h
  exact k.fullDim.labelling.targetEdge.symm.injective h

/-- A vertex of a connected graph with at least two vertices is an endpoint of
some occurrence. -/
theorem exists_incident_occurrence {G : CFGraph.{0}} (hConn : graph_connected G)
    [Nontrivial G.V] (v : G.V) :
    ∃ e : G.edges, ((e : G.V × G.V)).1 = v ∨ ((e : G.V × G.V)).2 = v := by
  classical
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨x, hx, y, hy, hpos⟩ :=
    hConn {v} ⟨v, w, Finset.mem_singleton_self v, by simpa using hw⟩
  have hxv : x = v := Finset.mem_singleton.mp hx
  obtain ⟨e, he⟩ := Count.TargetNormalForm.exists_occurrence hpos
  subst hxv
  rcases he with he | he
  · exact ⟨e, Or.inl (by rw [he])⟩
  · exact ⟨e, Or.inr (by rw [he])⟩

theorem FrameIso.targetVertex_self {k : Frame core degree} (fi : FrameIso k k)
    (v : k.target.V) : fi.datum.targetVertex v = v := by
  have := k.fullDim.nontrivial_target
  obtain ⟨e, he⟩ := exists_incident_occurrence k.fullDim.targetConnected v
  rcases he with he | he
  · have h := fi.datum.ends_fst e
    rw [fi.targetEdge_self e] at h
    rw [← he]
    exact h.symm
  · have h := fi.datum.ends_snd e
    rw [fi.targetEdge_self e] at h
    rw [← he]
    exact h.symm

/-! ### `FrameIso` is an equivalence relation -/

def FrameIso.refl (k : Frame core degree) : FrameIso k k where
  datum := Transport.DatumIso.refl k.data
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_refl, Equiv.refl_apply]
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_refl, Equiv.refl_apply]

def FrameIso.symm {k l : Frame core degree} (fi : FrameIso k l) : FrameIso l k where
  datum := fi.datum.symm
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_symm fi.datum k.fullDim.valid.1
      l.fullDim.valid.1]
    have hBack := fi.overCore_vertex
      ((fi.datum.branchVertexEquiv k.fullDim.valid.1).symm branch)
    rw [Equiv.apply_symm_apply] at hBack
    exact hBack.symm
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_symm fi.datum k.fullDim.valid.1
      l.fullDim.valid.1]
    have hBack := fi.overCore_row
      ((fi.datum.stablePathEquiv k.fullDim.valid.1).symm path)
    rw [Equiv.apply_symm_apply] at hBack
    exact hBack.symm

def FrameIso.trans {k l m : Frame core degree} (fi : FrameIso k l) (gi : FrameIso l m) :
    FrameIso k m where
  datum := fi.datum.trans gi.datum
  overCore_vertex branch := by
    rw [Transport.DatumIso.branchVertexEquiv_trans fi.datum gi.datum
      k.fullDim.valid.1 l.fullDim.valid.1, Equiv.trans_apply,
      gi.overCore_vertex, fi.overCore_vertex]
  overCore_row path := by
    rw [Transport.DatumIso.stablePathEquiv_trans fi.datum gi.datum
      k.fullDim.valid.1 l.fullDim.valid.1, Equiv.trans_apply,
      gi.overCore_row, fi.overCore_row]

/-! ## 2. Degeneracy: the geometric specialization -/

def Frame.DegenerateAt (k : Frame core degree) (y : Fin p → ℚ) (col : Fin p) : Prop :=
  k.coordsAt y col = 0 ∧ ∀ c, c ≠ col → 0 < k.coordsAt y c

theorem Frame.DegenerateAt.column_unique {k : Frame core degree} {y : Fin p → ℚ}
    {c c' : Fin p} (h : k.DegenerateAt y c) (h' : k.DegenerateAt y c') : c = c' := by
  by_contra hne
  exact absurd h.1 (ne_of_gt (h'.2 c hne))

theorem Frame.DegenerateAt.closed {k : Frame core degree} {y : Fin p → ℚ} {col : Fin p}
    (h : k.DegenerateAt y col) : (k.member y).Closed := by
  intro c
  by_cases hc : c = col
  · subst hc
    rw [Frame.coords_member, h.1]
  · exact (h.2 c hc).le

theorem Frame.DegenerateAt.not_open {k : Frame core degree} {y : Fin p → ℚ} {col : Fin p}
    (h : k.DegenerateAt y col) : ¬ (k.member y).Open := by
  intro hOpen
  have := hOpen col
  rw [Frame.coords_member, h.1] at this
  exact lt_irrefl 0 this

theorem Frame.DegenerateAt.map {k l : Frame core degree} (fi : FrameIso k l)
    {y : Fin p → ℚ} {col : Fin p} (h : k.DegenerateAt y col) :
    l.DegenerateAt y (fi.column col) := by
  refine ⟨?_, fun c hc ↦ ?_⟩
  · rw [fi.coordsAt_column y col]; exact h.1
  · have hback := fi.coordsAt_column y (fi.column.symm c)
    rw [Equiv.apply_symm_apply] at hback
    rw [hback]
    exact h.2 _ fun hcon ↦ hc (by rw [← hcon, Equiv.apply_symm_apply])

/-! ### The two sides of the wall -/

noncomputable def Frame.push (k : Frame core degree) (col : Fin p) : Fin p → ℚ :=
  fun s ↦ k.matrix (k.slot.symm s) col

theorem Frame.coordsAt_push (k : Frame core degree) (col : Fin p) :
    k.coordsAt (k.push col) = Pi.single col (1 : ℚ) := by
  have hmul : ∀ r : Fin p,
      k.matrix.mulVec (Pi.single col (1 : ℚ)) r = k.matrix r col := by
    intro r
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single col]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ col) hcon
  have h1 : (fun r ↦ (k.push col) (k.slot r)) = k.matrix.mulVec (Pi.single col (1 : ℚ)) := by
    funext r
    rw [hmul r]
    show k.matrix (k.slot.symm (k.slot r)) col = k.matrix r col
    rw [Equiv.symm_apply_apply]
  rw [Frame.coordsAt, h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ k.isUnit_det,
    Matrix.one_mulVec]

theorem Frame.coordsAt_add (k : Frame core degree) (y y' : Fin p → ℚ) (c : Fin p) :
    k.coordsAt (y + y') c = k.coordsAt y c + k.coordsAt y' c := by
  simp only [Frame.coordsAt_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by ring

theorem Frame.coordsAt_sub (k : Frame core degree) (y y' : Fin p → ℚ) (c : Fin p) :
    k.coordsAt (y - y') c = k.coordsAt y c - k.coordsAt y' c := by
  simp only [Frame.coordsAt_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun r _ ↦ by ring

theorem Frame.DegenerateAt.openAt_add_push {k : Frame core degree} {y : Fin p → ℚ}
    {col : Fin p} (h : k.DegenerateAt y col) : k.OpenAt (y + k.push col) := by
  intro c
  rw [Frame.coordsAt_add, Frame.coordsAt_push]
  by_cases hc : c = col
  · subst hc
    rw [h.1, Pi.single_eq_same]
    norm_num
  · rw [Pi.single_eq_of_ne hc]
    simpa using h.2 c hc

theorem Frame.DegenerateAt.coordsAt_sub_push {k : Frame core degree} {y : Fin p → ℚ}
    {col : Fin p} (h : k.DegenerateAt y col) :
    k.coordsAt (y - k.push col) col = -1 := by
  rw [Frame.coordsAt_sub, Frame.coordsAt_push, h.1, Pi.single_eq_same]
  norm_num

theorem Frame.DegenerateAt.not_openAt_sub_push {k : Frame core degree} {y : Fin p → ℚ}
    {col : Fin p} (h : k.DegenerateAt y col) : ¬ k.OpenAt (y - k.push col) := by
  intro hOpen
  have := hOpen col
  rw [h.coordsAt_sub_push] at this
  norm_num at this

/-! ### From the wall calculus of `SegmentWalls` to degeneracy -/

theorem Frame.degenerateAt_of_isWallParam (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) (u t : ℚ)
    (hopen : k.OpenAt (RationalAffineWall.segment y₀ y₁ u))
    (hwall : k.IsWallParam y₀ y₁ col t)
    (hno : ∀ c t', c ≠ col → min u t ≤ t' → t' ≤ max u t →
      ¬ k.IsWallParam y₀ y₁ c t') :
    k.DegenerateAt (RationalAffineWall.segment y₀ y₁ t) col :=
  ⟨hwall, fun c hc ↦ k.pos_of_pos_of_no_wall y₀ y₁ c u t (hopen c)
    fun t' h1 h2 ↦ hno c t' hc h1 h2⟩

/-! ## 3. The limit of a degeneration -/

/-- The target occurrence a coordinate names. -/
def Frame.edgeOf (k : Frame core degree) (col : Fin p) : k.target.edges :=
  k.fullDim.labelling.targetEdge col

/-- A full-dimensional presentation's target is a tree, so every coordinate's
occurrence is the only one joining its endpoints. -/
theorem Frame.numEdges_edgeOf (k : Frame core degree) (col : Fin p) :
    num_edges k.target ((k.edgeOf col : k.target.V × k.target.V)).1
      ((k.edgeOf col : k.target.V × k.target.V)).2 = 1 :=
  IteratedContraction.num_edges_eq_one_of_genus_zero_of_connected k.target
    k.fullDim.targetConnected k.fullDim.targetGenus _

/-- The target of the limit. -/
def Frame.limitTarget (k : Frame core degree) (col : Fin p) : CFGraph.{0} :=
  GluingContraction.contractTarget (k.edgeOf col) (k.numEdges_edgeOf col)

/-- The limit datum. -/
noncomputable def Frame.limit (k : Frame core degree) (col : Fin p) :
    GluingDatum (k.limitTarget col) degree :=
  GluingContraction.contractDatumAt k.data (k.edgeOf col) (k.numEdges_edgeOf col)

end DraismaVargas.Count.SegmentWalls

namespace DraismaVargas.Count.WallStar

open DraismaVargas.Infrastructure
open DraismaVargas.Count.SegmentWalls
open DraismaVargas.Count.Transport (DatumIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ} {core : Core n p} {degree : ℕ}

/-- A frame together with the coordinate it degenerates in. -/
structure Regrowth (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) where
  /-- The full-dimensional frame. -/
  frame : Frame core degree
  /-- The coordinate that vanishes. -/
  column : Fin p
  /-- Every other coordinate is positive. -/
  degenerate : frame.DegenerateAt y column

namespace Regrowth

variable {y : Fin p → ℚ}

/-- The limit datum of a regrowth. -/
noncomputable def limit (w : Regrowth core y degree) :
    GluingDatum (w.frame.limitTarget w.column) degree :=
  w.frame.limit w.column

/-- Two regrowths have the same limit. -/
def SameLimit (w w' : Regrowth core y degree) : Prop :=
  Nonempty (DatumIso w.limit w'.limit)

theorem SameLimit.refl (w : Regrowth core y degree) : SameLimit w w :=
  ⟨Transport.DatumIso.refl _⟩

theorem SameLimit.symm {w w' : Regrowth core y degree} (h : SameLimit w w') :
    SameLimit w' w := h.elim fun iso ↦ ⟨iso.symm⟩

theorem SameLimit.trans {w w' w'' : Regrowth core y degree} (h : SameLimit w w')
    (h' : SameLimit w' w'') : SameLimit w w'' :=
  h.elim fun iso ↦ h'.elim fun iso' ↦ ⟨iso.trans iso'⟩

/-- The setoid of limits. -/
def limitSetoid (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Setoid (Regrowth core y degree) where
  r := SameLimit
  iseqv := ⟨SameLimit.refl, SameLimit.symm, SameLimit.trans⟩

theorem openAt_add_push (w : Regrowth core y degree) :
    w.frame.OpenAt (y + w.frame.push w.column) := w.degenerate.openAt_add_push

theorem not_openAt_sub_push (w : Regrowth core y degree) :
    ¬ w.frame.OpenAt (y - w.frame.push w.column) := w.degenerate.not_openAt_sub_push

theorem closed (w : Regrowth core y degree) : (w.frame.member y).Closed :=
  w.degenerate.closed

theorem not_open (w : Regrowth core y degree) : ¬ (w.frame.member y).Open :=
  w.degenerate.not_open

end Regrowth

/-! ## 4. The star -/

/-- A member of the star of the codimension-one limit presented by `w`. -/
structure StarMember {y : Fin p → ℚ} (w : Regrowth core y degree) where
  /-- The regrowth. -/
  member : Regrowth core y degree
  /-- It specializes to the same limit. -/
  specializes : Regrowth.SameLimit member w

namespace StarMember

variable {y : Fin p → ℚ} {w : Regrowth core y degree}

/-- Two star members are the same facet when their frames are isomorphic over
the core. -/
def Rel (m m' : StarMember w) : Prop := Nonempty (FrameIso m.member.frame m'.member.frame)

theorem rel_equivalence : Equivalence (StarMember.Rel (w := w)) where
  refl _ := ⟨FrameIso.refl _⟩
  symm h := h.elim fun fi ↦ ⟨fi.symm⟩
  trans h h' := h.elim fun fi ↦ h'.elim fun gi ↦ ⟨fi.trans gi⟩

end StarMember

/-- The setoid of the star. -/
def starSetoid {y : Fin p → ℚ} (w : Regrowth core y degree) : Setoid (StarMember w) where
  r := StarMember.Rel
  iseqv := StarMember.rel_equivalence

/-- **The star of the codimension-one limit presented by `w`.** -/
def Star {y : Fin p → ℚ} (w : Regrowth core y degree) := Quotient (starSetoid w)

/-- The class of a star member. -/
def StarMember.cls {y : Fin p → ℚ} {w : Regrowth core y degree} (m : StarMember w) :
    Star w := Quotient.mk (starSetoid w) m

/-- **The star sits inside the labelled fibre at the wall request.** -/
noncomputable def Star.toFibre {y : Fin p → ℚ} {w : Regrowth core y degree}
    (s : Star w) : Fibre core y degree :=
  Quotient.liftOn s (fun m ↦ (m.member.frame.member y).cls) (by
    rintro m m' ⟨fi⟩
    exact FibreMember.cls_eq_cls_iff.mpr ⟨fi.toMemberIso y⟩)

@[simp] theorem Star.toFibre_cls {y : Fin p → ℚ} {w : Regrowth core y degree}
    (m : StarMember w) : Star.toFibre m.cls = (m.member.frame.member y).cls := rfl

theorem Star.toFibre_injective {y : Fin p → ℚ} {w : Regrowth core y degree} :
    Function.Injective (Star.toFibre (w := w)) := by
  intro s s'
  refine Quotient.inductionOn₂ s s' ?_
  intro m m' h
  have hiso : IsoOverCore (m.member.frame.member y) (m'.member.frame.member y) :=
    FibreMember.cls_eq_cls_iff.mp h
  exact Quotient.sound
    ((isoOverCore_member_iff m.member.frame m'.member.frame y).mp hiso)

instance Star.instFinite {y : Fin p → ℚ} (w : Regrowth core y degree) : Finite (Star w) :=
  Finite.of_injective _ (Star.toFibre_injective (w := w))

noncomputable instance Star.instFintype {y : Fin p → ℚ} (w : Regrowth core y degree) :
    Fintype (Star w) := Fintype.ofFinite _

/-- Every star is nonempty: the presenting regrowth is a member of its own
star. -/
def Regrowth.self {y : Fin p → ℚ} (w : Regrowth core y degree) : StarMember w :=
  ⟨w, Regrowth.SameLimit.refl w⟩

instance Star.instNonempty {y : Fin p → ℚ} (w : Regrowth core y degree) :
    Nonempty (Star w) := ⟨(Regrowth.self w).cls⟩

/-! ## 5. Membership is specialization -/

/-- **Specialization**: the frame `k` degenerates at `y` in the coordinate
`col`, and its limit there is isomorphic to the limit `w` presents. -/
def SpecializesTo (k : Frame core degree) (col : Fin p) {y : Fin p → ℚ}
    (w : Regrowth core y degree) : Prop :=
  k.DegenerateAt y col ∧ Nonempty (DatumIso (k.limit col) w.limit)

/-- **Membership is specialization.** -/
theorem specializesTo_iff_sameLimit {y : Fin p → ℚ} (w m : Regrowth core y degree) :
    SpecializesTo m.frame m.column w ↔ Regrowth.SameLimit m w :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨m.degenerate, h⟩⟩

/-- A specialization is a star member. -/
def SpecializesTo.starMember {k : Frame core degree} {col : Fin p} {y : Fin p → ℚ}
    {w : Regrowth core y degree} (h : SpecializesTo k col w) : StarMember w :=
  ⟨⟨k, col, h.1⟩, h.2⟩

/-- A star member specializes. -/
theorem specializesTo_of_starMember {y : Fin p → ℚ} {w : Regrowth core y degree}
    (m : StarMember w) : SpecializesTo m.member.frame m.member.column w :=
  ⟨m.member.degenerate, m.specializes⟩

/-- **Fixing the column is not a condition.**  Every isomorphism of frames over
the core carries the vanishing coordinate of one regrowth to the vanishing
coordinate of the other. -/
theorem column_eq_of_frameIso {y : Fin p → ℚ} {w w' : Regrowth core y degree}
    (fi : FrameIso w.frame w'.frame) : fi.column w.column = w'.column :=
  (w.degenerate.map fi).column_unique w'.degenerate

/-- Every class of the star lies in the closed cone of the fibre at the wall
request. -/
theorem Star.closed {y : Fin p → ℚ} {w : Regrowth core y degree} (s : Star w) :
    (Star.toFibre s).Closed := by
  refine Quotient.inductionOn s ?_
  intro m
  exact m.member.closed

/-- and in none of its open cones. -/
theorem Star.not_open {y : Fin p → ℚ} {w : Regrowth core y degree} (s : Star w) :
    ¬ (Star.toFibre s).Open := by
  refine Quotient.inductionOn s ?_
  intro m
  exact m.member.not_open

/-- The coordinate a star member degenerates in becomes `1` one unit along its
own push direction: the member is genuinely full-dimensional on that side. -/
theorem Regrowth.coordsAt_add_push_self {y : Fin p → ℚ} (w : Regrowth core y degree) :
    w.frame.coordsAt (y + w.frame.push w.column) w.column = 1 := by
  rw [Frame.coordsAt_add, Frame.coordsAt_push, w.degenerate.1, Pi.single_eq_same]
  norm_num

/-- and `-1` one unit along the other side. -/
theorem Regrowth.coordsAt_sub_push_self {y : Fin p → ℚ} (w : Regrowth core y degree) :
    w.frame.coordsAt (y - w.frame.push w.column) w.column = -1 :=
  w.degenerate.coordsAt_sub_push

/-- **From the segment calculus of `SegmentWalls` to the star.**  An open frame that
meets a wall at the parameter `t` in the coordinate `col`, and crosses none of
its own other walls in between, is a regrowth at the wall request. -/
def regrowthOfWallParam (k : Frame core degree) (y₀ y₁ : Fin p → ℚ)
    (col : Fin p) (u t : ℚ)
    (hopen : k.OpenAt (RationalAffineWall.segment y₀ y₁ u))
    (hwall : k.IsWallParam y₀ y₁ col t)
    (hno : ∀ c t', c ≠ col → min u t ≤ t' → t' ≤ max u t →
      ¬ k.IsWallParam y₀ y₁ c t') :
    Regrowth core (RationalAffineWall.segment y₀ y₁ t) degree :=
  ⟨k, col, k.degenerateAt_of_isWallParam y₀ y₁ col u t hopen hwall hno⟩

/-! ## 6. The limit as an invariant of the class -/

/-- **The limit is an invariant of the class.**  An isomorphism of frames over
the core induces an isomorphism of the two limit data.  It is *proved*
(`limitTransports`, section 10, from `contractDatumIso`), not assumed: nothing
in sections 3--5 uses it, and the star, its setoid, its `Fintype` and the
injection into the fibre are unconditional without it. -/
def LimitTransports (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ w w' : Regrowth core y degree, FrameIso w.frame w'.frame → Regrowth.SameLimit w w'

/-! ## 7. Non-vacuity, and what it shows -/

/-- The all-ones caterpillar request with the slot `j` driven to zero. -/
def catWallRequest (m : ℕ) (j : Fin (6 * m + 3)) : Fin (6 * m + 3) → ℚ :=
  RationalAffineWall.segment (catStart m) (catFinish m j) (1 / 2)

theorem catWallRequest_self (m : ℕ) (j : Fin (6 * m + 3)) : catWallRequest m j j = 0 := by
  show catStart m j + (1 / 2) * (catFinish m j j - catStart m j) = 0
  rw [catFinish, Function.update_self]
  show (1 : ℚ) + (1 / 2) * (-1 - 1) = 0
  norm_num

theorem catWallRequest_ne (m : ℕ) {j col : Fin (6 * m + 3)} (h : col ≠ j) :
    catWallRequest m j col = 1 := by
  show catStart m col + (1 / 2) * (catFinish m j col - catStart m col) = 1
  rw [catFinish, Function.update_of_ne h]
  show (1 : ℚ) + (1 / 2) * (1 - 1) = 1
  norm_num

theorem coordsAt_catWallRequest_ne (m : ℕ) {j col : Fin (6 * m + 3)} (h : col ≠ j) :
    0 < (catFrame m).coordsAt (catWallRequest m j) col := by
  rw [catWallRequest, Frame.coordsAt_segment, coordsAt_catStart,
    coordsAt_catFinish_ne m h, sub_self, mul_zero, add_zero]
  exact one_div_pos.mpr (FibreCaterpillar.catDiag_pos m col)

theorem catFrame_degenerateAt (m : ℕ) (j : Fin (6 * m + 3)) :
    (catFrame m).DegenerateAt (catWallRequest m j) j :=
  ⟨catFrame_wallParam m j, fun _ hc ↦ coordsAt_catWallRequest_ne m hc⟩

/-- **The non-vacuity witness.** -/
noncomputable def catRegrowth (m : ℕ) (j : Fin (6 * m + 3)) :
    Regrowth (FibreCaterpillar.catCore m) (catWallRequest m j) (m + 2) :=
  ⟨catFrame m, j, catFrame_degenerateAt m j⟩

example (m : ℕ) (j : Fin (6 * m + 3)) : Nonempty (Star (catRegrowth m j)) := inferInstance

example (m : ℕ) (j : Fin (6 * m + 3)) : Finite (Star (catRegrowth m j)) := inferInstance

/-- **What the witness is not.**  The caterpillar length matrix is diagonal, so
its coordinate vanishes exactly when the requested slot does: at every request
with all slots positive the caterpillar frame is open, and it presents no
codimension-one limit with a nondegenerate source. -/
theorem catFrame_not_degenerateAt_of_pos (m : ℕ) {y : Fin (6 * m + 3) → ℚ}
    (hy : ∀ s, 0 < y s) (col : Fin (6 * m + 3)) :
    ¬ (catFrame m).DegenerateAt y col := by
  intro h
  have hzero := h.1
  rw [coordsAt_catFrame_apply] at hzero
  rcases div_eq_zero_iff.mp hzero with hnum | hden
  · exact absurd hnum (ne_of_gt (hy col))
  · exact absurd hden (FibreCaterpillar.catDiag_ne_zero m col)

/-! ## 8. Sheet algebra: the join of the two endpoint partitions is natural -/

section JoinRelabel

open SheetPartition

variable {d : ℕ} {Pa Pb : SheetPartition d} {σa σb : Equiv.Perm (Fin d)}

theorem relabel_rel_symm_iff (P : SheetPartition d) (π : Equiv.Perm (Fin d)) (u v : Fin d) :
    (P.relabel π).Rel u v ↔ P.Rel (π.symm u) (π.symm v) := by
  have h := P.relabel_rel_iff π (π.symm u) (π.symm v)
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

theorem joinRel_relabel_of_joinRel
    (hlink : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    {x y : Fin d} (h : JoinRel Pa Pb x y) :
    JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σa y) := by
  induction h with
  | rel u v huv =>
      rcases huv with hl | hr
      · exact joinRel_of_left ((Pa.relabel_rel_iff σa u v).mpr hl)
      · exact ((hlink u).trans
          (joinRel_of_right ((Pb.relabel_rel_iff σb u v).mpr hr))).trans (hlink v).symm
  | refl u => exact joinRel_refl _ _ _
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

theorem joinRel_of_joinRel_relabel
    (hlink : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u))
    {u v : Fin d} (h : JoinRel (Pa.relabel σa) (Pb.relabel σb) u v) :
    JoinRel Pa Pb (σa.symm u) (σa.symm v) := by
  induction h with
  | rel x z hxz =>
      rcases hxz with hl | hr
      · exact joinRel_of_left ((relabel_rel_symm_iff Pa σa x z).mp hl)
      · exact ((hlink x).trans
          (joinRel_of_right ((relabel_rel_symm_iff Pb σb x z).mp hr))).trans (hlink z).symm
  | refl u => exact joinRel_refl _ _ _
  | symm u v _ ih => exact ih.symm
  | trans u v w _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The join is natural up to blocks.**  If the two endpoint partitions are
relabelled by permutations that agree modulo the join, the joins have the same
blocks after relabelling by either one. -/
theorem sameBlocks_join_relabel
    (hlinkQ : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    (hlinkP : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u)) :
    ((join Pa Pb).relabel σa).SameBlocks (join (Pa.relabel σa) (Pb.relabel σb)) := by
  intro u v
  rw [relabel_rel_symm_iff, join_rel_iff, join_rel_iff]
  constructor
  · intro h
    have := joinRel_relabel_of_joinRel hlinkQ h
    rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  · exact joinRel_of_joinRel_relabel hlinkP

/-- The permutation that turns the relabelled join into the join of the
relabelled parts **on the nose**, not merely blockwise.  It is needed because
`SheetPartition` stores a rigid representative map and `join` picks the least
element of each class, a choice that no permutation commutes with. -/
noncomputable def mergePerm
    (hlinkQ : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    (hlinkP : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u)) : Equiv.Perm (Fin d) :=
  σa.trans (PartitionNormalization.permutation _ _ (sameBlocks_join_relabel hlinkQ hlinkP))

theorem relabel_mergePerm
    (hlinkQ : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    (hlinkP : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u)) :
    (join Pa Pb).relabel (mergePerm hlinkQ hlinkP) = join (Pa.relabel σa) (Pb.relabel σb) := by
  rw [mergePerm, ← SheetPartition.relabel_relabel]
  exact PartitionNormalization.relabel_eq _ _ (sameBlocks_join_relabel hlinkQ hlinkP)

theorem join_rel_mergePerm_symm
    (hlinkQ : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    (hlinkP : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u)) (t : Fin d) :
    (join Pa Pb).Rel ((mergePerm hlinkQ hlinkP).symm t) (σa.symm t) := by
  have h := PartitionNormalization.permutation_symm_rel
    ((join Pa Pb).relabel σa) (join (Pa.relabel σa) (Pb.relabel σb))
    (sameBlocks_join_relabel hlinkQ hlinkP) t
  rw [relabel_rel_symm_iff] at h
  exact h

theorem merged_rel_mergePerm_symm
    (hlinkQ : ∀ x, JoinRel (Pa.relabel σa) (Pb.relabel σb) (σa x) (σb x))
    (hlinkP : ∀ u, JoinRel Pa Pb (σa.symm u) (σb.symm u)) {t s : Fin d}
    (h : (join Pa Pb).Rel (σa.symm t) s ∨ (join Pa Pb).Rel (σb.symm t) s) :
    (join Pa Pb).Rel ((mergePerm hlinkQ hlinkP).symm t) s := by
  have hstep := join_rel_mergePerm_symm hlinkQ hlinkP t
  rcases h with h | h
  · exact hstep.trans h
  · exact hstep.trans (((join_rel_iff Pa Pb _ _).mpr (hlinkP t)).trans h)

end JoinRelabel

/-! ## 9. Contraction is functorial for `DatumIso` -/

section LimitTransport

open GluingContraction GraphContraction SheetPartition

variable {target₁ target₂ : CFGraph.{0}} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- The vertices of the two contracted targets correspond. -/
def contractVertexEquiv (iso : DatumIso first second) (e₁ : target₁.edges) :
    Vertex target₁ ((e₁ : target₁.V × target₁.V)).2 ≃
      Vertex target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 where
  toFun x := ⟨iso.targetVertex x.1, by
    rw [iso.ends_snd e₁]
    exact fun h ↦ x.2 (iso.targetVertex.injective h)⟩
  invFun w := ⟨iso.targetVertex.symm w.1, by
    intro h
    apply w.2
    have hstep : iso.targetVertex (iso.targetVertex.symm w.1)
        = iso.targetVertex ((e₁ : target₁.V × target₁.V)).2 := congrArg _ h
    rw [Equiv.apply_symm_apply] at hstep
    exact hstep.trans (iso.ends_snd e₁).symm⟩
  left_inv x := by
    apply Subtype.ext
    exact Equiv.symm_apply_apply _ _
  right_inv w := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ _

@[simp] theorem contractVertexEquiv_val (iso : DatumIso first second) (e₁ : target₁.edges)
    (x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) :
    (contractVertexEquiv iso e₁ x).1 = iso.targetVertex x.1 := rfl

theorem contractVertexEquiv_fold (iso : DatumIso first second) (e₁ : target₁.edges)
    (v : target₁.V) :
    contractVertexEquiv iso e₁ (fold target₁ (fst_ne_snd e₁) v)
      = fold target₂ (fst_ne_snd (iso.targetEdge e₁)) (iso.targetVertex v) := by
  apply Subtype.ext
  rw [contractVertexEquiv_val]
  by_cases hv : v = ((e₁ : target₁.V × target₁.V)).2
  · have h1 : (fold target₁ (fst_ne_snd e₁) v).1 = ((e₁ : target₁.V × target₁.V)).1 := by
      rw [hv, fold_self]
    have h2 : iso.targetVertex v = ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 := by
      rw [iso.ends_snd e₁, hv]
    have h3 : (fold target₂ (fst_ne_snd (iso.targetEdge e₁)) (iso.targetVertex v)).1
        = ((iso.targetEdge e₁ : target₂.V × target₂.V)).1 := by
      rw [h2, fold_self]
    rw [h1, h3, iso.ends_fst e₁]
  · have hne : iso.targetVertex v ≠ ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 := by
      rw [iso.ends_snd e₁]
      exact fun h ↦ hv (iso.targetVertex.injective h)
    rw [fold_of_ne _ _ hv, fold_of_ne _ _ hne]

/-- The occurrences of the two contracted targets correspond. -/
noncomputable def contractEdgeEquiv (iso : DatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1) :
    (contractTarget e₁ hOne₁).edges ≃ (contractTarget (iso.targetEdge e₁) hOne₂).edges :=
  (foldEdgeEquiv rfl (fst_ne_snd e₁) hOne₁).symm.trans
    ((Equiv.subtypeEquiv iso.targetEdge (fun f ↦ by
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq])).trans
      (foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂))

theorem unfoldEdge_contractEdgeEquiv (iso : DatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) :
    unfoldEdge rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂
        (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê)
      = iso.targetEdge (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) := by
  show ((foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂).symm
      ((foldEdgeEquiv rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂)
        ((Equiv.subtypeEquiv iso.targetEdge _)
          ((foldEdgeEquiv rfl (fst_ne_snd e₁) hOne₁).symm ê)))).1 = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem contractVertexPartition_of_eq {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (a b : target.V)
    {y : Vertex target b} (h : (y : target.V) = a) :
    contractVertexPartition data a b y
      = join (data.vertexPartition a) (data.vertexPartition b) := if_pos h

/-- The two endpoint sheet permutations of a `DatumIso` agree modulo the join
of the endpoint partitions of the occurrence, downstairs. -/
theorem joinRel_vertexPerm_symm (iso : DatumIso first second) (e₁ : target₁.edges)
    (u : Fin degree) :
    JoinRel (first.vertexPartition ((e₁ : target₁.V × target₁.V)).1)
      (first.vertexPartition ((e₁ : target₁.V × target₁.V)).2)
      ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1).symm u)
      ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2).symm u) := by
  have h1 := iso.compatible_fst e₁ ((iso.edgePerm e₁).symm u)
  have h2 := iso.compatible_snd e₁ ((iso.edgePerm e₁).symm u)
  rw [Equiv.apply_symm_apply] at h1 h2
  exact (joinRel_of_left h1).trans (joinRel_of_right h2).symm

/-- and upstairs. -/
theorem joinRel_vertexPerm (iso : DatumIso first second) (e₁ : target₁.edges)
    (x : Fin degree) :
    JoinRel
      ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).1).relabel
        (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1))
      ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).2).relabel
        (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2))
      (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1 x)
      (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2 x) := by
  have k1 := ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).1).relabel_rel_iff
    (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1)
    ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).1).symm (iso.edgePerm e₁ x)) x).mpr
      (iso.compatible_fst e₁ x)
  have k2 := ((first.vertexPartition ((e₁ : target₁.V × target₁.V)).2).relabel_rel_iff
    (iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2)
    ((iso.vertexPerm ((e₁ : target₁.V × target₁.V)).2).symm (iso.edgePerm e₁ x)) x).mpr
      (iso.compatible_snd e₁ x)
  rw [Equiv.apply_symm_apply] at k1 k2
  exact (joinRel_of_left k1).symm.trans (joinRel_of_right k2)

/-- The sheet permutation the contracted datum carries at the merged vertex. -/
noncomputable def mergedPerm (iso : DatumIso first second) (e₁ : target₁.edges) :
    Equiv.Perm (Fin degree) :=
  mergePerm (joinRel_vertexPerm iso e₁) (joinRel_vertexPerm_symm iso e₁)

/-- The sheet permutations of the contracted datum. -/
noncomputable def contractVertexPerm (iso : DatumIso first second) (e₁ : target₁.edges)
    (x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : Equiv.Perm (Fin degree) :=
  if (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1 then mergedPerm iso e₁
  else iso.vertexPerm (x : target₁.V)

theorem contractVertexPerm_merged (iso : DatumIso first second) (e₁ : target₁.edges)
    {x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2}
    (hx : (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1) :
    contractVertexPerm iso e₁ x = mergedPerm iso e₁ := if_pos hx

theorem contractVertexPerm_of_ne (iso : DatumIso first second) (e₁ : target₁.edges)
    {x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2}
    (hx : (x : target₁.V) ≠ ((e₁ : target₁.V × target₁.V)).1) :
    contractVertexPerm iso e₁ x = iso.vertexPerm (x : target₁.V) := if_neg hx

theorem contractDatumIso_vertexPartition (iso : DatumIso first second) (e₁ : target₁.edges)
    (x : Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) :
    contractVertexPartition second ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
        ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 (contractVertexEquiv iso e₁ x)
      = (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
          ((e₁ : target₁.V × target₁.V)).2 x).relabel (contractVertexPerm iso e₁ x) := by
  by_cases hx : (x : target₁.V) = ((e₁ : target₁.V × target₁.V)).1
  · have hx2 : ((contractVertexEquiv iso e₁ x : Vertex target₂
          ((iso.targetEdge e₁ : target₂.V × target₂.V)).2) : target₂.V)
        = ((iso.targetEdge e₁ : target₂.V × target₂.V)).1 := by
      rw [contractVertexEquiv_val, hx, iso.ends_fst e₁]
    rw [contractVertexPartition_of_eq _ _ _ hx2, contractVertexPartition_of_eq _ _ _ hx,
      contractVertexPerm_merged iso e₁ hx, mergedPerm, relabel_mergePerm,
      iso.ends_fst e₁, iso.ends_snd e₁, iso.vertexPartition, iso.vertexPartition]
  · have hx2 : ((contractVertexEquiv iso e₁ x : Vertex target₂
          ((iso.targetEdge e₁ : target₂.V × target₂.V)).2) : target₂.V)
        ≠ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1 := by
      rw [contractVertexEquiv_val, iso.ends_fst e₁]
      exact fun h ↦ hx (iso.targetVertex.injective h)
    rw [contractVertexPartition_of_ne _ _ _ hx2, contractVertexPartition_of_ne _ _ _ hx,
      contractVertexPerm_of_ne iso e₁ hx, contractVertexEquiv_val]
    exact iso.vertexPartition _

theorem contractDatumIso_compatible_fst (iso : DatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) (s : Fin degree) :
    (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
        ((e₁ : target₁.V × target₁.V)).2
        ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1).Rel
      ((contractVertexPerm iso e₁
          ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1).symm
        (iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s)) s := by
  have hfst : ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).1
      = fold target₁ (fst_ne_snd e₁)
        ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :=
    (congrArg Prod.fst (fold_unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).symm
  rw [hfst]
  by_cases hv : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1
      = ((e₁ : target₁.V × target₁.V)).2
  · have hfold : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((e₁ : target₁.V × target₁.V)).1 := by
      rw [hv, fold_self]
    rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
      mergedPerm]
    refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
      (joinRel_vertexPerm_symm iso e₁) (Or.inr ?_)
    have hc := iso.compatible_fst (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s
    rw [hv] at hc
    exact (join_rel_iff _ _ _ _).mpr (joinRel_of_right hc)
  · have hfoldval : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 := by
      rw [fold_of_ne _ _ hv]
    by_cases hva : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1
        = ((e₁ : target₁.V × target₁.V)).1
    · have hfold := hfoldval.trans hva
      rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
        mergedPerm]
      refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
        (joinRel_vertexPerm_symm iso e₁) (Or.inl ?_)
      have hc := iso.compatible_fst (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s
      rw [hva] at hc
      exact (join_rel_iff _ _ _ _).mpr (joinRel_of_left hc)
    · have hne : ((fold target₁ (fst_ne_snd e₁)
            ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).1 :
          Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
          ≠ ((e₁ : target₁.V × target₁.V)).1 := by
        rw [hfoldval]; exact hva
      rw [contractVertexPartition_of_ne _ _ _ hne, contractVertexPerm_of_ne iso e₁ hne,
        hfoldval]
      exact iso.compatible_fst _ s

theorem contractDatumIso_compatible_snd (iso : DatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (ê : (contractTarget e₁ hOne₁).edges) (s : Fin degree) :
    (contractVertexPartition first ((e₁ : target₁.V × target₁.V)).1
        ((e₁ : target₁.V × target₁.V)).2
        ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2).Rel
      ((contractVertexPerm iso e₁
          ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2).symm
        (iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s)) s := by
  have hsnd : ((ê : (contractTarget e₁ hOne₁).V × (contractTarget e₁ hOne₁).V)).2
      = fold target₁ (fst_ne_snd e₁)
        ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :=
    (congrArg Prod.snd (fold_unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).symm
  rw [hsnd]
  by_cases hv : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2
      = ((e₁ : target₁.V × target₁.V)).2
  · have hfold : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((e₁ : target₁.V × target₁.V)).1 := by
      rw [hv, fold_self]
    rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
      mergedPerm]
    refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
      (joinRel_vertexPerm_symm iso e₁) (Or.inr ?_)
    have hc := iso.compatible_snd (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s
    rw [hv] at hc
    exact (join_rel_iff _ _ _ _).mpr (joinRel_of_right hc)
  · have hfoldval : ((fold target₁ (fst_ne_snd e₁)
          ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
        Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
        = ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 := by
      rw [fold_of_ne _ _ hv]
    by_cases hva : ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2
        = ((e₁ : target₁.V × target₁.V)).1
    · have hfold := hfoldval.trans hva
      rw [contractVertexPartition_of_eq _ _ _ hfold, contractVertexPerm_merged iso e₁ hfold,
        mergedPerm]
      refine merged_rel_mergePerm_symm (joinRel_vertexPerm iso e₁)
        (joinRel_vertexPerm_symm iso e₁) (Or.inl ?_)
      have hc := iso.compatible_snd (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê) s
      rw [hva] at hc
      exact (join_rel_iff _ _ _ _).mpr (joinRel_of_left hc)
    · have hne : ((fold target₁ (fst_ne_snd e₁)
            ((unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê : target₁.V × target₁.V)).2 :
          Vertex target₁ ((e₁ : target₁.V × target₁.V)).2) : target₁.V)
          ≠ ((e₁ : target₁.V × target₁.V)).1 := by
        rw [hfoldval]; exact hva
      rw [contractVertexPartition_of_ne _ _ _ hne, contractVertexPerm_of_ne iso e₁ hne,
        hfoldval]
      exact iso.compatible_snd _ s

/-- **Contraction is functorial.**  An isomorphism of gluing data carrying one
target occurrence to another induces an isomorphism of the two contracted data.
The merged vertex is the only place where the sheet permutation has to be
adjusted (`mergedPerm`), because `SheetPartition.join` chooses the least
representative of each merged class and no permutation commutes with that
choice. -/
noncomputable def contractDatumIso (iso : DatumIso first second) (e₁ : target₁.edges)
    (hOne₁ : num_edges target₁ ((e₁ : target₁.V × target₁.V)).1
      ((e₁ : target₁.V × target₁.V)).2 = 1)
    (hOne₂ : num_edges target₂ ((iso.targetEdge e₁ : target₂.V × target₂.V)).1
      ((iso.targetEdge e₁ : target₂.V × target₂.V)).2 = 1) :
    DatumIso (contractDatumAt first e₁ hOne₁)
      (contractDatumAt second (iso.targetEdge e₁) hOne₂) where
  targetVertex := contractVertexEquiv iso e₁
  targetEdge := contractEdgeEquiv iso e₁ hOne₁ hOne₂
  ends_fst ê := by
    have hf := fold_unfoldEdge (contracted := e₁) rfl (fst_ne_snd e₁) hOne₁ ê
    have hg := fold_unfoldEdge (contracted := iso.targetEdge e₁) rfl
      (fst_ne_snd (iso.targetEdge e₁)) hOne₂ (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê)
    rw [unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê] at hg
    rw [(congrArg Prod.fst hg).symm, (congrArg Prod.fst hf).symm]
    dsimp only
    exact (congrArg (fold target₂ (fst_ne_snd (iso.targetEdge e₁))) (iso.ends_fst _)).trans
      (contractVertexEquiv_fold iso e₁ _).symm
  ends_snd ê := by
    have hf := fold_unfoldEdge (contracted := e₁) rfl (fst_ne_snd e₁) hOne₁ ê
    have hg := fold_unfoldEdge (contracted := iso.targetEdge e₁) rfl
      (fst_ne_snd (iso.targetEdge e₁)) hOne₂ (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê)
    rw [unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê] at hg
    rw [(congrArg Prod.snd hg).symm, (congrArg Prod.snd hf).symm]
    dsimp only
    exact (congrArg (fold target₂ (fst_ne_snd (iso.targetEdge e₁))) (iso.ends_snd _)).trans
      (contractVertexEquiv_fold iso e₁ _).symm
  vertexPerm := contractVertexPerm iso e₁
  edgePerm ê := iso.edgePerm (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)
  vertexPartition := contractDatumIso_vertexPartition iso e₁
  edgePartition ê := by
    show second.edgePartition (unfoldEdge rfl (fst_ne_snd (iso.targetEdge e₁)) hOne₂
        (contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê))
      = (first.edgePartition (unfoldEdge rfl (fst_ne_snd e₁) hOne₁ ê)).relabel _
    rw [unfoldEdge_contractEdgeEquiv iso e₁ hOne₁ hOne₂ ê]
    exact iso.edgePartition _
  compatible_fst := contractDatumIso_compatible_fst iso e₁ hOne₁
  compatible_snd := contractDatumIso_compatible_snd iso e₁ hOne₁

end LimitTransport



/-! ## 10.  The limit is an invariant of the class -/

theorem FrameIso.targetEdge_edgeOf {k l : Frame core degree} (fi : FrameIso k l)
    (col : Fin p) : fi.datum.targetEdge (k.edgeOf col) = l.edgeOf (fi.column col) := by
  show fi.datum.targetEdge (k.fullDim.labelling.targetEdge col)
    = l.fullDim.labelling.targetEdge (fi.column col)
  rw [FrameIso.column, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]

noncomputable def contractDatumAt_congr {target : CFGraph.{0}} {degree : ℕ}
    (data : GluingDatum target degree) {e e' : target.edges} (h : e = e')
    (hOne : num_edges target ((e : target.V × target.V)).1
      ((e : target.V × target.V)).2 = 1)
    (hOne' : num_edges target ((e' : target.V × target.V)).1
      ((e' : target.V × target.V)).2 = 1) :
    DatumIso (GluingContraction.contractDatumAt data e hOne)
      (GluingContraction.contractDatumAt data e' hOne') := by
  subst h
  exact Transport.DatumIso.refl _

/-- **The limit datum only depends on the class of the frame.**  This is the
statement `LimitTransports` names. -/
theorem limitTransports (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    LimitTransports core y degree := by
  intro w w' fi
  have hE : fi.datum.targetEdge (w.frame.edgeOf w.column) = w'.frame.edgeOf w'.column := by
    rw [FrameIso.targetEdge_edgeOf fi w.column, column_eq_of_frameIso fi]
  have hOne₂ : num_edges w'.frame.target
      ((fi.datum.targetEdge (w.frame.edgeOf w.column) : w'.frame.target.V ×
        w'.frame.target.V)).1
      ((fi.datum.targetEdge (w.frame.edgeOf w.column) : w'.frame.target.V ×
        w'.frame.target.V)).2 = 1 := by
    rw [hE]
    exact w'.frame.numEdges_edgeOf w'.column
  exact ⟨(contractDatumIso fi.datum (w.frame.edgeOf w.column)
      (w.frame.numEdges_edgeOf w.column) hOne₂).trans
    (contractDatumAt_congr w'.frame.data hE hOne₂ (w'.frame.numEdges_edgeOf w'.column))⟩

/-- **Specialization is a property of the class**, not of the representative. -/
theorem specializesTo_map {k l : Frame core degree} {col : Fin p} {y : Fin p → ℚ}
    {w : Regrowth core y degree} (h : SpecializesTo k col w) (fi : FrameIso k l) :
    SpecializesTo l (fi.column col) w := by
  refine ⟨h.1.map fi, ?_⟩
  exact (limitTransports core y degree ⟨k, col, h.1⟩ ⟨l, fi.column col, h.1.map fi⟩ fi).symm.trans
    h.2

/-- **The star is saturated for `FrameIso`**, unconditionally. -/
def StarMember.ofFrameIso {y : Fin p → ℚ} {w : Regrowth core y degree} (m : StarMember w)
    (w' : Regrowth core y degree) (fi : FrameIso w'.frame m.member.frame) : StarMember w :=
  ⟨w', (limitTransports core y degree w' m.member fi).trans m.specializes⟩

/-- A class of the fibre at the wall request that some star member represents. -/
def IsStarClass {y : Fin p → ℚ} (w : Regrowth core y degree) (cls : Fibre core y degree) :
    Prop :=
  ∃ m : StarMember w, (m.member.frame.member y).cls = cls

/-- **Membership is specialization, on the quotient.**  The star is exactly the
set of classes of the labelled fibre at the wall request that specialize to the
limit `w` presents: the quotient by isomorphisms of `φ` fixing the column is
the subtype of the fibre cut out by specialization. -/
noncomputable def Star.equivSubtype {y : Fin p → ℚ} (w : Regrowth core y degree) :
    Star w ≃ {cls : Fibre core y degree // IsStarClass w cls} :=
  Equiv.ofBijective (fun s ↦ ⟨Star.toFibre s, by
      refine Quotient.inductionOn s ?_
      intro m
      exact ⟨m, rfl⟩⟩)
    ⟨fun s s' h ↦ Star.toFibre_injective (congrArg Subtype.val h), by
      rintro ⟨cls, m, hm⟩
      exact ⟨m.cls, Subtype.ext hm⟩⟩

/-- Every regrowth representing a star class specializes to the same limit. -/
theorem sameLimit_of_cls_eq {y : Fin p → ℚ} {w : Regrowth core y degree} (m : StarMember w)
    (m' : Regrowth core y degree)
    (h : (m'.frame.member y).cls = (m.member.frame.member y).cls) :
    Regrowth.SameLimit m' w := by
  have hiso : Nonempty (FrameIso m'.frame m.member.frame) :=
    (isoOverCore_member_iff _ _ y).mp (FibreMember.cls_eq_cls_iff.mp h)
  exact hiso.elim fun fi ↦
    (limitTransports core y degree m' m.member fi).trans m.specializes

/-- **Membership is specialization, class by class.**  A class of the labelled
fibre at the wall request belongs to the star of `w` exactly when the regrowth
representing it specializes to the limit `w` presents. -/
theorem isStarClass_iff {y : Fin p → ℚ} (w m : Regrowth core y degree) :
    IsStarClass w (m.frame.member y).cls ↔ Regrowth.SameLimit m w := by
  constructor
  · rintro ⟨m', hm'⟩
    exact sameLimit_of_cls_eq m' m hm'.symm
  · intro h
    exact ⟨⟨m, h⟩, rfl⟩

/-! ## 11.  What a Part II codimension-one limit additionally asks -/

/-- The requested metric graph is nondegenerate: every core slot has positive
length.  A `Regrowth` at a nondegenerate request is a codimension-one limit in
Part II's sense -- only the *target* edge collapses. -/
def Nondegenerate (y : Fin p → ℚ) : Prop := ∀ s, 0 < y s

/-- **The caterpillar wall is not one.**  Its length matrix is diagonal, so the
only way to make a coordinate vanish is to drive the requested slot to zero. -/
theorem not_nondegenerate_catWallRequest (m : ℕ) (j : Fin (6 * m + 3)) :
    ¬ Nondegenerate (catWallRequest m j) := by
  intro h
  have hj := h j
  rw [catWallRequest_self] at hj
  exact lt_irrefl 0 hj

/-- **At a nondegenerate request the vanishing coordinate is an admissible
column** in the sense of `LocalCases.InteriorProgress.AdmissibleColumn`: the
coordinate vector itself is a nonnegative chart point vanishing there whose
stable rows are all nonzero.  That is the hypothesis Part I's ten-way interior
classification consumes, so a Part II codimension-one limit is always in its
scope.  Stated here in unfolded form so that this file does not import the
march. -/
theorem admissibleColumn_of_degenerateAt {k : Frame core degree} {y : Fin p → ℚ}
    {col : Fin p} (h : k.DegenerateAt y col) (hy : Nondegenerate y) :
    ∃ z : Fin p → ℚ, (∀ c, 0 ≤ z c) ∧ z col = 0 ∧
      ∀ row, k.matrix.mulVec z row ≠ 0 := by
  refine ⟨k.coordsAt y, h.closed, h.1, fun row ↦ ?_⟩
  rw [k.mulVec_coordsAt y]
  exact ne_of_gt (hy (k.slot row))

end DraismaVargas.Count.WallStar
