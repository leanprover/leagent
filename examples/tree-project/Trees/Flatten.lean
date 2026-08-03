import Trees.Basic
import Trees.ListSum

/-!
# Flattening a tree

The middle layer. `flatten` is the in-order traversal and `total` sums the
labels directly; the two lemmas here tie them back to `size` and `sumList`.

This file imports both base files, so anything proved on top of it has a
dependency closure spanning the whole project.
-/

namespace Trees
namespace Tree

/-- In-order traversal. -/
def flatten : Tree → List Nat
  | .leaf => []
  | .node l v r => l.flatten ++ [v] ++ r.flatten

/-- Sum of every label, computed on the tree directly. -/
def total : Tree → Nat
  | .leaf => 0
  | .node l v r => l.total + v + r.total

/-- Flattening produces one element per node. -/
theorem length_flatten (t : Tree) : t.flatten.length = t.size := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp [flatten, size, ihl, ihr]
    omega

/-- Summing the traversal agrees with summing the tree. -/
theorem sum_flatten (t : Tree) : sumList t.flatten = t.total := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp [flatten, total, sumList_append, sumList, ihl, ihr]
    omega

end Tree
end Trees
