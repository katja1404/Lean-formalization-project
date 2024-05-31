import Mathlib

inductive binary_tree : Type
| leaf: binary_tree
| node₁: binary_tree → binary_tree
| node₂: binary_tree → binary_tree → binary_tree

/- The height of a binary tree-/

def binary_tree.height : binary_tree → ℕ
| leaf => 1
| node₁ T => T.height + 1
| node₂ T1 T2 => max T1.height T2.height + 1

/- The type of full binary trees-/

inductive full_binary_treee : Type
| leaf: full_binary_tree
| node₂: (T1 T2 : full_binary_tree) → full_binary_tree

/- The height of a full binary tree-/

def full_binary_tree.height : full_binary_tree → ℕ
| leaf => 1
| node₂ T1 T2 => max T1.height T2.height + 1

/- The num of nodes including leaves of a full binary tree-/

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1

def binary_tree_of_full_binary_tree: full_binary_tree → binary_tree
| .leaf => .leaf
| .node₂ T1 T2 => .node₂ (binary_tree_of_full_binary_tree T1) (binary_tree_of_full_binary_tree T2)

theorem eq_height_binary_tree_of_full_binary_tree:
  (T: full_binary_tree) →
  T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction T with
| leaf => rfl
| node₂ T1 T2 HT1 HT2 =>
  simp [full_binry_tree.height, binary_tree.height]
  rw[HT1, HT2]

theorem eq_number_of_nodes_binary_tree_of_full_binary_tree :
  (T: full_binary_tree) →
  T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
  sorry
