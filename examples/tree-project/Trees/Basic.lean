/-!
# Binary trees

The base layer: the `Tree` datatype and two functions over it, `size` and
`mirror`. Nothing here imports anything from the project, so this file is the
root of the dependency chain.
-/

namespace Trees

/-- A binary tree with a `Nat` at each internal node. -/
inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

namespace Tree

/-- Number of internal nodes. -/
def size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

/-- Reflect a tree left-to-right. -/
def mirror : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node r.mirror v l.mirror

/-- Mirroring preserves the number of nodes. -/
theorem size_mirror (t : Tree) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    simp [mirror, size, ihl, ihr]
    omega

/-- Mirroring is an involution. -/
theorem mirror_mirror (t : Tree) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [mirror, ihl, ihr]

end Tree

end Trees
