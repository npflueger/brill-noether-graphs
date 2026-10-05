module

public import DraismaVargas.Infrastructure.SheetGluing
public import DraismaVargas.Infrastructure.Change

@[expose] public section

/-!
# Genus change when the fresh sheet is glued

The Cools--Draisma tripod first grafts three source leaf families, then adds
one sheet and glues it at the three new target leaves. The harmonic graft
preserves genus; this file counts the second operation. A new sheet adds one
source edge per target edge and one source vertex per unglued target vertex.
Hence

`genus(new source) = genus(old source) + genus(target) - 1 + #glued vertices`.

This is an unconditional Euler identity. For a tree target and three glued
vertices it gives genus `+2`; `addSheetGluedOn_valid` separately guarantees
that the new source is connected and satisfies Riemann--Hurwitz.
-/

namespace DraismaVargas.Infrastructure

namespace SheetPartition

variable {degree : ℕ}

/-- Count canonical block representatives by their indicator function. -/
theorem card_blocks_eq_sum_fixed (partition : SheetPartition degree) :
    Fintype.card partition.Blocks =
      ∑ sheet : Fin degree, if partition.repr sheet = sheet then 1 else 0 := by
  change Fintype.card {sheet : Fin degree // partition.repr sheet = sheet} = _
  rw [Fintype.card_subtype, Finset.card_filter]

/-- An unglued fresh sheet contributes one additional block. -/
theorem card_blocks_addSheet (partition : SheetPartition degree) :
    Fintype.card partition.addSheet.Blocks = Fintype.card partition.Blocks + 1 := by
  rw [card_blocks_eq_sum_fixed, Fin.sum_univ_castSucc, card_blocks_eq_sum_fixed]
  simp only [addSheet_repr_castSucc, Fin.castSucc_inj, addSheet_repr_last,
    ite_true]

/-- Gluing the fresh sheet leaves every old canonical representative unchanged. -/
theorem gluedPartition_repr_castSucc (partition : SheetPartition degree)
    (old sheet : Fin degree) :
    (partition.gluedPartition (some old)).repr sheet.castSucc =
      (partition.repr sheet).castSucc := by
  change (if partition.addSheet.Rel (Fin.last degree) sheet.castSucc then
    partition.addSheet.repr old.castSucc else
    partition.addSheet.repr sheet.castSucc) = _
  rw [ite_eq_right (fun h ↦ partition.addSheet_not_rel_castSucc_last sheet h.symm),
    addSheet_repr_castSucc]

/-- The fresh sheet acquires the representative of the chosen old block. -/
theorem gluedPartition_repr_last (partition : SheetPartition degree)
    (old : Fin degree) :
    (partition.gluedPartition (some old)).repr (Fin.last degree) =
      (partition.repr old).castSucc := by
  change (if partition.addSheet.Rel (Fin.last degree) (Fin.last degree) then
    partition.addSheet.repr old.castSucc else
    partition.addSheet.repr (Fin.last degree)) = _
  rw [ite_eq_left (show partition.addSheet.Rel (Fin.last degree) (Fin.last degree)
    from rfl), addSheet_repr_castSucc]

/-- A glued fresh sheet creates no new block. -/
theorem card_blocks_gluedPartition_some (partition : SheetPartition degree)
    (old : Fin degree) :
    Fintype.card (partition.gluedPartition (some old)).Blocks =
      Fintype.card partition.Blocks := by
  rw [card_blocks_eq_sum_fixed, Fin.sum_univ_castSucc, card_blocks_eq_sum_fixed]
  simp only [gluedPartition_repr_castSucc, Fin.castSucc_inj,
    gluedPartition_repr_last, (Fin.castSucc_lt_last (partition.repr old)).ne,
    ite_false, add_zero]

/-- Uniform additive block count, avoiding truncated subtraction. -/
theorem card_blocks_gluedPartition_add (partition : SheetPartition degree)
    (choice : Option (Fin degree)) :
    Fintype.card (partition.gluedPartition choice).Blocks +
        (if choice.isSome then 1 else 0) =
      Fintype.card partition.Blocks + 1 := by
  cases choice with
  | none =>
      change Fintype.card partition.addSheet.Blocks + 0 =
        Fintype.card partition.Blocks + 1
      exact (Nat.add_zero _).trans (card_blocks_addSheet partition)
  | some old =>
      simp only [Option.isSome_some, ite_true]
      exact congrArg (fun n ↦ n + 1) (card_blocks_gluedPartition_some partition old)

end SheetPartition

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- Target vertices at which the choice function attaches the fresh sheet.
They are counted once each, regardless of which old block was chosen. -/
def gluedVertices (choice : target.V → Option (Fin degree)) : Finset target.V :=
  Finset.univ.filter fun vertex ↦ (choice vertex).isSome

@[simp] theorem mem_gluedVertices (choice : target.V → Option (Fin degree))
    (vertex : target.V) :
    vertex ∈ gluedVertices choice ↔ (choice vertex).isSome := by
  simp [gluedVertices]

/-- Every target edge acquires precisely one new source occurrence. -/
theorem card_sourceEdge_addSheetGluedOn (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) :
    Fintype.card (data.addSheetGluedOn choice).SourceEdge =
      Fintype.card data.SourceEdge + target.edges.card := by
  rw [card_sourceEdge_eq_sum_card_blocks, card_sourceEdge_eq_sum_card_blocks]
  calc
    (∑ edge : target.edges,
        Fintype.card ((data.addSheetGluedOn choice).edgePartition edge).Blocks) =
      ∑ edge : target.edges,
        (Fintype.card (data.edgePartition edge).Blocks + 1) := by
      apply Finset.sum_congr rfl
      intro edge _
      exact SheetPartition.card_blocks_addSheet (data.edgePartition edge)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Every unglued target vertex acquires one source vertex; glued vertices
acquire none. The additive form remains valid even if no vertex is glued. -/
theorem card_sourceVertex_addSheetGluedOn_add (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) :
    Fintype.card (data.addSheetGluedOn choice).SourceVertex +
        (gluedVertices choice).card =
      Fintype.card data.SourceVertex + Fintype.card target.V := by
  rw [card_sourceVertex_eq_sum_card_blocks, card_sourceVertex_eq_sum_card_blocks]
  rw [gluedVertices, Finset.card_filter, ← Finset.sum_add_distrib]
  calc
    (∑ vertex : target.V,
        (Fintype.card ((data.addSheetGluedOn choice).vertexPartition vertex).Blocks +
          if (choice vertex).isSome then 1 else 0)) =
      ∑ vertex : target.V, (Fintype.card (data.vertexPartition vertex).Blocks + 1) := by
      apply Finset.sum_congr rfl
      intro vertex _
      exact SheetPartition.card_blocks_gluedPartition_add
        (data.vertexPartition vertex) (choice vertex)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- The exact Euler change under a partially glued degree raise. No
connectedness, validity or target-tree hypotheses are needed for the count. -/
theorem genus_sourceGraph_addSheetGluedOn (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree)) :
    genus (data.addSheetGluedOn choice).sourceGraph =
      genus data.sourceGraph + genus target - 1 + (gluedVertices choice).card := by
  have hEdges := data.card_sourceEdge_addSheetGluedOn choice
  have hVertices := data.card_sourceVertex_addSheetGluedOn_add choice
  simp only [genus, sourceGraph_edges_card]
  change ((Fintype.card (data.addSheetGluedOn choice).SourceEdge : ℤ) -
      (Fintype.card (data.addSheetGluedOn choice).SourceVertex : ℤ) + 1) =
    ((Fintype.card data.SourceEdge : ℤ) -
      (Fintype.card data.SourceVertex : ℤ) + 1) +
      ((target.edges.card : ℤ) - (Fintype.card target.V : ℤ) + 1) - 1 + _
  omega

/-- The three-leaf gluing in a tripod raises the source genus by exactly two. -/
theorem genus_sourceGraph_addSheetGluedOn_three (data : GluingDatum target degree)
    (choice : target.V → Option (Fin degree))
    (hTree : genus target = 0) (hThree : (gluedVertices choice).card = 3) :
    genus (data.addSheetGluedOn choice).sourceGraph = genus data.sourceGraph + 2 := by
  rw [genus_sourceGraph_addSheetGluedOn, hTree, hThree]
  push_cast
  ring

end GluingDatum

end DraismaVargas.Infrastructure
