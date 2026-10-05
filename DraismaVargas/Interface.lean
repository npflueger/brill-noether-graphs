module

public import DraismaVargas.Basic
public import Utilities.Gonality.SubdivisionPencil
public import DraismaVargas.Infrastructure.TargetTreePotential
public import Utilities.Harmonic.Basic
public import Utilities.Iso.FossilTopology
public import Utilities.Subdivision.LeafExtension
public import Utilities.Subdivision.PathSplitRefinement

@[expose] public section

/-!
# Checked interfaces for the Draisma--Vargas construction

The load-bearing boundary is divisor-first: a rank-one Brill--Noether witness
on one regular subdivision bounds `regularSubdivisionGonality`.  This is the
interface for generated affine certificates.

The rest of the file verifies the intended upstream composition.  A finite
chain of leaf additions models a tree attachment, a single
`LaplacianEquiv` permits arbitrary vertex labels, and a harmonic map to a
connected genus-zero target produces the rank-one witness.  The general
harmonic theorem explicitly asks for `PullbackPrincipalCompatible`; the
Boolean checker proves that condition only for unit edge indices.
Thus denominator clearing is not silently presented as a proof for arbitrary
nonunit dilation indices.
-/

namespace DraismaVargas

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Gonality

/-- A graph obtained from `base` by finitely many explicit leaf additions.
Iterated additions attach an arbitrary finite rooted tree, one leaf at a time.
-/
inductive LeafExtensionChain : CFGraph → CFGraph → Prop
  | refl (G : CFGraph) : LeafExtensionChain G G
  | addLeaf {G H : CFGraph} (chain : LeafExtensionChain G H) (root : H.V) :
      LeafExtensionChain G (LeafExtension.addLeaf H root)

namespace LeafExtensionChain

/-- Every-rank Brill--Noether existence is unchanged along a finite chain of
leaf additions. -/
theorem bnExists_iff {G H : CFGraph} (chain : LeafExtensionChain G H)
    (r d : ℤ) : BNExists H r d ↔ BNExists G r d := by
  induction chain with
  | refl => rfl
  | addLeaf chain root ih =>
      exact (LeafExtension.bnExists_addLeaf_iff _ root r d).trans ih

end LeafExtensionChain

/-- A labelled presentation of a tropical modification by tree attachment.

The intermediate `presentation` is literally a leaf-extension chain from the
base graph; `relabeling` allows the modified source used by a harmonic
certificate to have unrelated vertex labels. -/
structure TreeModification (base modified : CFGraph) where
  presentation : CFGraph
  relabeling : LaplacianEquiv modified presentation
  chain : LeafExtensionChain base presentation

namespace TreeModification

/-- Regard a literal leaf-extension chain as a tree modification, with no
relabeling overhead. -/
def ofLeafExtensionChain {G H : CFGraph} (chain : LeafExtensionChain G H) :
    TreeModification G H where
  presentation := H
  relabeling :=
    { toEquiv := Equiv.refl _
      num_edges_eq := by intro x y; rfl }
  chain := chain

/-- Every-rank Brill--Noether existence descends through a finite tree
modification. -/
theorem bnExists_iff {G H : CFGraph} (modification : TreeModification G H)
    (r d : ℤ) : BNExists H r d ↔ BNExists G r d :=
  (modification.relabeling.bnExists_iff r d).trans
    (modification.chain.bnExists_iff r d)

end TreeModification

/-- The narrow load-bearing boundary for certified constructions: a rank-one
witness on one regular subdivision gives the corresponding upper bound. -/
theorem regularSubdivisionGonality_le_of_BNExists_scale
    {n p d k : ℕ} (spec : Spec n p) (hk : 0 < k)
    (hBN : BNExists (spec.scale k hk).graph 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  obtain ⟨w, _⟩ := SubdivisionPencil.exists_of_BNExists hk hBN
  exact w.gonality_le

/-- A rank-one witness on any checked positive bivalent refinement of a
regular subdivision bounds the original metric model.

This is the boundary at which a generated certificate is lowered directly.  The
generated presentation may use
arbitrary vertex and edge labels: `RefinementPresentation.relabeling` carries
that final finite identification after the canonical split chain. -/
theorem regularSubdivisionGonality_le_of_refinementPresentation
    {n p d k : ℕ} {spec : Spec n p} (hk : 0 < k) {G : CFGraph}
    (presentation : RefinementPresentation
      ({ n := n, p := p, spec := spec.scale k hk } : PackedSpec) G)
    (hBN : BNExists G 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_BNExists_scale spec hk
  exact (presentation.bnExists_iff 1 (d : ℤ)).mpr hBN

/-- A rank-one witness on a tree modification of a regular subdivision
descends to the subdivision and therefore bounds the original metric model. -/
theorem regularSubdivisionGonality_le_of_treeModification
    {n p d k : ℕ} {spec : Spec n p} (hk : 0 < k) {G : CFGraph}
    (modification : TreeModification (spec.scale k hk).graph G)
    (hBN : BNExists G 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_BNExists_scale spec hk
  exact (modification.bnExists_iff 1 (d : ℤ)).mp hBN

/-- A rank-one witness on the fossil of a connected regular subdivision is
already enough to bound the original metric model.

This is the canonical bridge/tree-pruning boundary: a certificate generator
may discard every separating edge at once instead of presenting an ordered
chain of leaf additions.  `TreeModification` remains available when the
explicit attached-tree presentation is itself part of the certificate. -/
theorem regularSubdivisionGonality_le_of_fossil
    {n p d k : ℕ} {spec : Spec n p} (hk : 0 < k)
    (hConnected : graph_connected (spec.scale k hk).graph)
    (hBN : BNExists (fossil (spec.scale k hk).graph) 1 (d : ℤ)) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_BNExists_scale spec hk
  exact (BNExists_fossil_iff (spec.scale k hk).graph hConnected 1 (d : ℤ)).mpr
    hBN

/-- End-to-end composition for a harmonic map from a tree modification of a
regular subdivision to a connected genus-zero target.

`PullbackPrincipalCompatible` is the exact weighted-Laplacian hypothesis used
by the public harmonic theorem.  It is automatic for the unit-indexed checked
certificates in the next corollary. -/
theorem regularSubdivisionGonality_le_of_harmonic_tree
    {n p d k : ℕ} {spec : Spec n p} (hk : 0 < k)
    {G T : CFGraph} (f : MarkedGraphs.IndexedHarmonicData G T)
    (modification : TreeModification (spec.scale k hk).graph G)
    (hDegree : f.HasDegree (d : ℤ))
    (hPullback : f.PullbackPrincipalCompatible)
    (hTargetConnected : graph_connected T) (hTargetGenus : genus T = 0)
    (z : T.V) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_treeModification hk modification
  exact f.bnExists_rank_one_of_connected_genus_zero_target hDegree hPullback
    hTargetConnected hTargetGenus z

/-- Boolean-replayed unit-indexed version of the end-to-end harmonic
composition.  Only target connectedness and genus zero remain structural
proof inputs. -/
theorem regularSubdivisionGonality_le_of_checked_unit_harmonic_tree
    {n p d k : ℕ} {spec : Spec n p} (hk : 0 < k)
    {G T : CFGraph} (c : MarkedGraphs.IndexedHarmonicCertificate G T)
    (modification : TreeModification (spec.scale k hk).graph G)
    (hCheck : c.check = true) (hUnitCheck : c.checkUnitIndexed = true)
    (hDegreeCheck : c.checkDegree (d : ℤ) = true)
    (hTargetConnected : graph_connected T) (hTargetGenus : genus T = 0)
    (z : T.V) :
    spec.regularSubdivisionGonality ≤ d := by
  apply regularSubdivisionGonality_le_of_treeModification hk modification
  exact MarkedGraphs.IndexedHarmonicData.bnExists_rank_one_of_checked_harmonic_tree
    c (d : ℤ) hCheck hUnitCheck hDegreeCheck hTargetConnected hTargetGenus z

/-! ## Constructive Part-I endpoint -/

/-- The finite object whose existence is sufficient for the Part-I bound.

The realized quotient source may contain tree modifications of the requested
regular subdivision, so the identification is recorded with the existing
`TreeModification` interface rather than as literal graph equality. -/
structure IntegralGluingConstruction {n p : ℕ} (spec : Spec n p)
    (degree : ℕ) where
  scale : ℕ
  scale_pos : 0 < scale
  target : CFGraph
  data : Infrastructure.GluingDatum target degree
  realization : data.IntegralRealization
  sourceModification :
    TreeModification (spec.scale scale scale_pos).graph realization.sourceSpec.graph
  sourceConnected : data.Connected
  targetConnected : graph_connected target
  targetGenus : genus target = 0

namespace IntegralGluingConstruction

/-- A finite integral gluing construction produces the promised regular
subdivision gonality bound, with all divisor semantics discharged by the
uniform target-tree theorem. -/
theorem regularSubdivisionGonality_le {n p degree : ℕ} {spec : Spec n p}
    (construction : IntegralGluingConstruction spec degree) :
    spec.regularSubdivisionGonality ≤ degree := by
  apply regularSubdivisionGonality_le_of_treeModification
    construction.scale_pos construction.sourceModification
  exact (construction.realization.bnExists_and_effective_of_connected_genus_zero_target
      construction.sourceConnected construction.targetConnected
      construction.targetGenus
      (Classical.choice (inferInstance : Nonempty construction.target.V))).1

end IntegralGluingConstruction

end DraismaVargas
