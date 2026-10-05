module

-- Treewidth and gonality: the van Dobben de Bruyn--Gijswijt theorem
-- `treewidth <= gonality` (arXiv:1407.7055) and the Seymour--Thomas
-- bramble/treewidth duality it rests on.
--
-- This application library imports only `Utilities` and external dependencies.
-- Its declarations use the `Utilities.Treewidth` and `Utilities.Gonality`
-- namespaces.

-- Tree decompositions, brambles, and Seymour--Thomas duality.
public import TreewidthGonality.Treewidth.TreeDecomposition
public import TreewidthGonality.Treewidth.Bramble
public import TreewidthGonality.Treewidth.PartialDecomposition
public import TreewidthGonality.Treewidth.TreePath
public import TreewidthGonality.Treewidth.Separation
public import TreewidthGonality.Treewidth.SeymourThomasInduction
public import TreewidthGonality.Treewidth.SeymourThomas

-- The divisor-theoretic half, and the assembled theorem.
public import TreewidthGonality.Gonality.BrambleGonality
public import TreewidthGonality.Gonality.TreewidthGonality

-- A one-file public interface: the library's main theorems restated in full
-- and checked by the kernel against the real declarations.
public import TreewidthGonality.Highlights

@[expose] public section
