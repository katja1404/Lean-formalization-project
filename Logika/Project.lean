import Mathlib
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic



--------- Small Tasks ---------


-- 1. Catalan Numbers --

open BigOperators

def catalan_number: (n : ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i) * (catalan_number (n-i))

-- #eval catalan_number 5


-- 2. Plane Trees --

section plane_tree

open List

inductive plane_tree: Type
| node : (List plane_tree) → plane_tree

end plane_tree


-- def plane_tree.definicija : plane_tree -> List plane_tree
-- | .node N => N


-- 3. Full Binary Trees --

inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂: (T1 T2 : full_binary_tree) → full_binary_tree

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => max T1.height T2.height + 1

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1


-- 4. Full Binary Trees with n nodes --

inductive full_binary_tree_with_n_nodes : (n : ℕ) → Type
| leaf : full_binary_tree_with_n_nodes 0
| node: {m n : ℕ} → full_binary_tree_with_n_nodes m → full_binary_tree_with_n_nodes n → full_binary_tree_with_n_nodes (n + m + 1)


-- 5. Ballot Sequences of Length n --

inductive ballot_sequence : ℕ → ℕ → Type
| empty : ballot_sequence 0 0
| add_zero : {zeros ones : ℕ} → ballot_sequence zeros ones → ballot_sequence (zeros + 1) ones
| add_one : {zeros ones : ℕ} → ballot_sequence zeros ones → zeros > ones → ballot_sequence zeros (ones + 1)




--------- Larger Tasks ---------



-- 3. Bijection between full binary trees and the type Fin Cn --

-- kr tezka :/

-- def full_binary_tree_to_fin_Cn : full_binary_tree_with_n_nodes (n : ℕ) → (n : Fin (catalan_number n))
-- | .leaf => 0
-- | .node =>



-- 4. Bijection Between list PlaneTree and PlaneTree

-- ideja: definiraš 2 funkciji (def):
--    - List PlaneTree -> PlaneTree
--    - PlaneTree -> List PlaneTree
--
-- in pokažeš (theorem) da če uporabiš najprej eno in pol drugo, da dobiš nazaj isto

def plane_tree_to_list_plane_tree : plane_tree → List plane_tree
| .node N => N

def list_plane_tree_to_plane_tree : List plane_tree → plane_tree
| N => .node N

theorem plane_tree_of_list_plane_tree_of_plane_tree_is_id :
∀ (t : plane_tree), list_plane_tree_to_plane_tree (plane_tree_to_list_plane_tree t) = t := by
intro x
cases x
case node N => rfl

theorem list_plane_tree_of_plane_tree_of_list_plane_tree_is_id :
∀ (t : List plane_tree), plane_tree_to_list_plane_tree (list_plane_tree_to_plane_tree t) = t := by
exact fun t ↦ rfl



-- 6. 2n choose n is divisible by n+1 --

-- #eval Nat.choose 10 2

lemma two_n_minus_n_eq_n (n : ℕ) :
2 * n - n = n := by
omega

lemma two_n_minus_n_plus_one_eq_n_minus_one (n : ℕ) :
2 * n - (n + 1) = n - 1 := by
omega

lemma one_over_n_minus_one_factorial_eq_n_over_n_factorial (n : ℕ) :
1 / Nat.factorial (n - 1) = n / Nat.factorial n := by
sorry

lemma equality (n : ℕ):
Nat.choose (2 * n) (n + 1) = n / (n + 1) * Nat.choose (2 * n) n := by
rw [Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial]
rw [two_n_minus_n_eq_n, two_n_minus_n_plus_one_eq_n_minus_one]
apply Nat.div_eq_of_eq_mul_right
sorry
rw [← mul_assoc]
apply Nat.eq_mul_of_div_eq_left











theorem n_plus_one_divides_2n_choose_n (n : ℕ) :
n + 1 ∣ Nat.choose (2 * n) n := by
sorry
