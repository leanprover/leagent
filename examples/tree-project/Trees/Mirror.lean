import Trees.Flatten

/-!
# Mirroring, and the headline result

The top layer. `flatten_mirror` says the traversal of a mirrored tree is the
reversed traversal, and `total_mirror` — the headline theorem — concludes that
mirroring leaves the sum of the labels alone.

`total_mirror` is the interesting extraction target: its proof reaches into
every other file in the project.
-/

namespace Trees
namespace Tree

/-- Mirroring reverses the in-order traversal. -/
theorem flatten_mirror (t : Tree) : t.mirror.flatten = t.flatten.reverse := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mirror, flatten, ihl, ihr]

/-- Mirroring preserves the sum of the labels. -/
theorem total_mirror (t : Tree) : t.mirror.total = t.total := by
  rw [← sum_flatten, ← sum_flatten, flatten_mirror, sumList_reverse]

/-- The two `size` facts combine: a mirrored tree flattens to a list of the
same length. -/
theorem length_flatten_mirror (t : Tree) : t.mirror.flatten.length = t.size := by
  rw [length_flatten, size_mirror]

end Tree
end Trees
