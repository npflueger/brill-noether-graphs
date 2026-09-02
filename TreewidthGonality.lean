-- Treewidth and gonality: the van Dobben de Bruyn--Gijswijt theorem
-- `treewidth <= gonality` (arXiv:1407.7055) and the Seymour--Thomas
-- bramble/treewidth duality it rests on.
--
-- This application library imports only `Utilities` and external dependencies.
-- Its declarations use the `Utilities.Treewidth` and `Utilities.Gonality`
-- namespaces.

-- Tree decompositions, brambles, and Seymour--Thomas duality.
import TreewidthGonality.Treewidth.TreeDecomposition
import TreewidthGonality.Treewidth.Bramble
import TreewidthGonality.Treewidth.PartialDecomposition
import TreewidthGonality.Treewidth.TreePath
import TreewidthGonality.Treewidth.Separation
import TreewidthGonality.Treewidth.SeymourThomasInduction
import TreewidthGonality.Treewidth.SeymourThomas

-- The divisor-theoretic half, and the assembled theorem.
import TreewidthGonality.Gonality.BrambleGonality
import TreewidthGonality.Gonality.TreewidthGonality

-- A one-file public interface: the library's main theorems restated in full
-- and checked by the kernel against the real declarations.
import TreewidthGonality.Highlights
