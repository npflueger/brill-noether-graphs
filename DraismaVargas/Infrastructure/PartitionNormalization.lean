module

public import DraismaVargas.Infrastructure.GluingRelabel

@[expose] public section

/-!
# Normalize stored representatives without changing any sheet block

Equal block relations do not imply equal representative maps. On each common
block, transpose the two chosen representatives. These disjoint transpositions
form an involution preserving every block, and conjugate the first stored
partition to the second exactly. Applying this independently at all target
vertices and occurrences gives compatible sheet relabelling of gluing data.
-/

namespace DraismaVargas.Infrastructure.PartitionNormalization

variable {degree : ℕ} (first second : SheetPartition degree)

def adjust (sheet : Fin degree) : Fin degree :=
  Equiv.swap (first.repr sheet) (second.repr sheet) sheet

theorem adjust_rel (hSame : first.SameBlocks second) (sheet : Fin degree) :
    first.Rel (adjust first second sheet) sheet := by
  apply first.swap_apply_rel_self_of_rel
  exact (first.rel_repr_left sheet).trans
    ((hSame sheet (second.repr sheet)).mpr (second.rel_repr_right sheet))

theorem adjust_second_rel (hSame : first.SameBlocks second) (sheet : Fin degree) :
    second.Rel (adjust first second sheet) sheet :=
  (hSame _ _).mp (adjust_rel first second hSame sheet)

theorem adjust_involutive (hSame : first.SameBlocks second) :
    Function.Involutive (adjust first second) := by
  intro sheet
  change Equiv.swap (first.repr (adjust first second sheet))
    (second.repr (adjust first second sheet)) (adjust first second sheet) = sheet
  rw [show first.repr (adjust first second sheet) = first.repr sheet from
    adjust_rel first second hSame sheet,
    show second.repr (adjust first second sheet) = second.repr sheet from
      adjust_second_rel first second hSame sheet]
  exact Equiv.swap_apply_self _ _ _

/-- This actual within-block permutation is its own inverse. -/
def permutation (hSame : first.SameBlocks second) : Equiv.Perm (Fin degree) where
  toFun := adjust first second
  invFun := adjust first second
  left_inv := adjust_involutive first second hSame
  right_inv := adjust_involutive first second hSame

theorem permutation_rel (hSame : first.SameBlocks second) (sheet : Fin degree) :
    first.Rel (permutation first second hSame sheet) sheet :=
  adjust_rel first second hSame sheet

theorem permutation_symm_rel (hSame : first.SameBlocks second) (sheet : Fin degree) :
    first.Rel ((permutation first second hSame).symm sheet) sheet :=
  adjust_rel first second hSame sheet

theorem permutation_repr (hSame : first.SameBlocks second) (sheet : Fin degree) :
    permutation first second hSame (first.repr sheet) = second.repr sheet := by
  change Equiv.swap (first.repr (first.repr sheet))
    (second.repr (first.repr sheet)) (first.repr sheet) = second.repr sheet
  rw [first.repr_idem,
    show second.repr (first.repr sheet) = second.repr sheet from
      (hSame _ _).mp (first.rel_repr_left sheet)]
  exact Equiv.swap_apply_left _ _

/-- Conjugating by the actual normalization permutation yields equality of
stored partitions, not merely another equivalent relation. -/
theorem relabel_eq (hSame : first.SameBlocks second) :
    first.relabel (permutation first second hSame) = second := by
  apply SheetPartition.ext_repr
  funext sheet
  change permutation first second hSame
    (first.repr ((permutation first second hSame).symm sheet)) = second.repr sheet
  rw [show first.repr ((permutation first second hSame).symm sheet) = first.repr sheet from
    permutation_symm_rel first second hSame sheet]
  exact permutation_repr first second hSame sheet

section Gluing

variable {target : CFGraph} (data other : GluingDatum target degree)
  (hVertices : ∀ vertex, (data.vertexPartition vertex).SameBlocks (other.vertexPartition vertex))
  (hEdges : ∀ edge, (data.edgePartition edge).SameBlocks (other.edgePartition edge))

/-- Independent blockwise normalizations satisfy the genuine edge-to-vertex
compatibility: edge permutations stay within the finer original edge block. -/
def sheetRelabeling : data.SheetRelabeling where
  vertexPermutation vertex := permutation _ _ (hVertices vertex)
  edgePermutation edge := permutation _ _ (hEdges edge)
  compatible_left edge sheet :=
    (permutation_symm_rel _ _ (hVertices edge.1.1) _).trans
      ((data.refines_left edge).rel (permutation_rel _ _ (hEdges edge) sheet))
  compatible_right edge sheet :=
    (permutation_symm_rel _ _ (hVertices edge.1.2) _).trans
      ((data.refines_right edge).rel (permutation_rel _ _ (hEdges edge) sheet))

theorem sheetRelabeling_apply : (sheetRelabeling data other hVertices hEdges).apply = other := by
  have hV : (sheetRelabeling data other hVertices hEdges).apply.vertexPartition =
      other.vertexPartition := by
    funext vertex
    exact relabel_eq _ _ (hVertices vertex)
  have hE : (sheetRelabeling data other hVertices hEdges).apply.edgePartition =
      other.edgePartition := by
    funext edge
    exact relabel_eq _ _ (hEdges edge)
  cases hFirst : (sheetRelabeling data other hVertices hEdges).apply
  cases other
  simp only [hFirst] at hV hE
  cases hV
  cases hE
  rfl

/-- The normalization carries the quotient vertex named by a sheet to the
other representative of that very sheet's block. -/
theorem sourceVertexEquiv_sourceEndpoint_val (vertex : target.V) (sheet : Fin degree) :
    ((sheetRelabeling data other hVertices hEdges).sourceVertexEquiv
      (data.sourceEndpoint vertex sheet)).1 =
        (vertex, (other.vertexPartition vertex).repr sheet) :=
  Prod.ext rfl (permutation_repr _ _ (hVertices vertex) sheet)

/-- The actual occurrence and sheet-block correspondence is explicit;
it is not an arbitrary bijection of equal-cardinality quotient sets. -/
theorem sourceEdgeEquiv_sourceEdge_val (edge : target.edges) (sheet : Fin degree) :
    ((sheetRelabeling data other hVertices hEdges).sourceEdgeEquiv
      (data.sourceEdge edge sheet)).1 =
        (edge, (other.edgePartition edge).repr sheet) :=
  Prod.ext rfl (permutation_repr _ _ (hEdges edge) sheet)

end Gluing

end DraismaVargas.Infrastructure.PartitionNormalization
