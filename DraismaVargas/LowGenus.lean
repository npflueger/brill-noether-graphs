import DraismaVargas.Basic
import Utilities.Gonality.SubdivisionPencil
import LowGenus.AtanasovRanganathanExistence

/-!
# The Draisma--Vargas bound through genus five, at scale one

These are consequences of the discrete Atanasov--Ranganathan theorem proved in
the `LowGenus` library; no Draisma--Vargas cone certificate is needed to
establish these bounds.
-/

namespace DraismaVargas

open Utilities
open Utilities.Certificate.SubdivisionGraph
open Utilities.Gonality

/-- Every positive subdivision of a connected genus-four core has a
degree-three pencil already at scale one. -/
theorem genusFour_regularSubdivisionGonality_le_three {n p : ℕ} (spec : Spec n p) (hgenus : p = n + 3)
    (hconn : graph_connected spec.graph) :
    spec.regularSubdivisionGonality ≤ 3 := by
  have hG : genus spec.graph = 4 := by
    rw [spec.genus_graph, hgenus]; push_cast; ring
  have hBN : BNExists spec.graph 1 3 :=
    AtanasovRanganathan.genusFourRankOneExistence spec.graph hconn hG
  have hDgon : divisorialGonality spec.graph ≤ 3 := by
    exact_mod_cast divisorialGonality_le_of_BNExists hBN
  exact spec.regularSubdivisionGonality_le_divisorialGonality.trans hDgon

/-- A discrete pencil through genus five, before forgetting its divisor. -/
theorem throughFive_bnExists_one_ceil_half_genus_add_one {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hg : p + 1 - n ≤ 5) :
    BNExists spec.graph 1 (((p + 2 - n) / 2 + 1 : ℕ) : ℤ) := by
  have hn := core_vertices_le_edges_add_one spec hconn
  have hG : genus spec.graph ≤ 5 := by
    rw [spec.genus_graph]; omega
  have hρ := AtanasovRanganathan.brillNoetherExistenceThroughFive spec.graph hconn hG
    1 (((p + 2 - n) / 2 + 1 : ℕ) : ℤ)
  obtain ⟨D, hrank, hdeg⟩ := hρ (by
    simp only [spec.genus_graph]
    omega)
  exact ⟨D, hdeg, hrank⟩

/-- The low-genus construction retains an effective divisor and scale one. -/
theorem throughFive_subdivisionPencil_at_one {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hg : p + 1 - n ≤ 5) :
    ∃ w : SubdivisionPencil spec ((p + 2 - n) / 2 + 1), w.scale = 1 :=
  SubdivisionPencil.exists_at_one
    (throughFive_bnExists_one_ceil_half_genus_add_one spec hconn hg)

/-- The all-genus statement, restricted to genus at most five, at scale one. -/
theorem throughFive_regularSubdivisionGonality_le_ceil_half_genus_add_one {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hg : p + 1 - n ≤ 5) :
    spec.regularSubdivisionGonality ≤ (p + 2 - n) / 2 + 1 := by
  obtain ⟨w, _⟩ := throughFive_subdivisionPencil_at_one spec hconn hg
  exact w.gonality_le

end DraismaVargas
