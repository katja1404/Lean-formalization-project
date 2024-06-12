import Mathlib
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic


--------- ########### ---------
--------- Small Tasks ---------
--------- ########### ---------

-- ################## --
-- 1. Catalan Numbers --
-- ################## --

open BigOperators

def catalan_number: (n : ℕ) → ℕ
| 0 => 1
| n+1 => ∑ i : Fin (n+1), (catalan_number i) * (catalan_number (n-i))


-- ############## --
-- 2. Plane Trees --
-- ############## --

section plane_tree

open List

inductive plane_tree: Type
| node : (List plane_tree) → plane_tree

end plane_tree


-- #################### --
-- 3. Full Binary Trees --
-- #################### --

inductive full_binary_tree: Type
| leaf : full_binary_tree
| node₂: (T1 T2 : full_binary_tree) → full_binary_tree

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => max T1.height T2.height + 1

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| .node₂ T1 T2 => T1.number_of_nodes + T2.number_of_nodes + 1


-- ################################# --
-- 4. Full Binary Trees with n nodes --
--################################## --

inductive full_binary_tree_with_n_nodes : (n : ℕ) → Type
| leaf : full_binary_tree_with_n_nodes 0
| node: {m n : ℕ} → full_binary_tree_with_n_nodes m → full_binary_tree_with_n_nodes n → full_binary_tree_with_n_nodes (n + m + 1)


-- ############################### --
-- 5. Ballot Sequences of Length n --
-- ############################### --

inductive ballot_sequence : ℕ → ℕ → Type
| empty : ballot_sequence 0 0
| add_zero : {zeros ones : ℕ} → ballot_sequence zeros ones → ballot_sequence (zeros + 1) ones
| add_one : {zeros ones : ℕ} → ballot_sequence zeros ones → zeros > ones → ballot_sequence zeros (ones + 1)



--------- ############ ---------
--------- Larger Tasks ---------
--------- ############ ---------


-- ################################################# --
-- 4. Bijection Between list PlaneTree and PlaneTree --
-- ################################################# --

-- Idea: define two functions:
--    - f  : List PlaneTree -> PlaneTree
--    - f' : PlaneTree -> List PlaneTree
--
-- and show that f(f'(x)) = x and f'(f(x)) = x

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


-- ################################## --
-- 6. 2n choose n is divisible by n+1 --
-- ################################## --


-- We tried to follow this proof: https://math.stackexchange.com/a/189350
-- Our idea was to first prove the equality - lemma "equality"

lemma two_n_minus_n_eq_n (n : ℕ) :
2 * n - n = n := by
omega

lemma two_n_minus_n_plus_one_eq_n_minus_one (n : ℕ) :
2 * n - (n + 1) = n - 1 := by
omega

lemma equality (n : ℕ) (h : n > 0):
Nat.choose (2 * n) (n + 1) = n / (n + 1) * Nat.choose (2 * n) n := by
  rw [Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial]
  rw [two_n_minus_n_eq_n, two_n_minus_n_plus_one_eq_n_minus_one]
  apply Nat.div_eq_of_eq_mul_right
  apply Nat.mul_pos
  apply Nat.factorial_pos
  apply Nat.factorial_pos
  rw [Nat.factorial_succ]
  -- At this point the proof is obvious on paper.
  -- We first wanted to cancel the n+1 one the right, as it appears once in the denominator and once normally.
  -- The problem is that this seems impossible in lean - the division used is division with remainder, which makes
  -- the lemma false and therefore non-provable.
  sorry
  omega
  omega

-- We may try to solve this problem by casting one of the factors to a rational number - for example n+1, which
-- forces the division to operate using rationals. The lemma is therefore true, but it is questionable if it can
-- be proved.
lemma equality_q (n : ℕ) (h : n > 0):
Nat.choose (2 * n) (n + 1) = n / ((n + 1) : ℚ) * Nat.choose (2 * n) n := by
  rw [Nat.choose_eq_factorial_div_factorial, Nat.choose_eq_factorial_div_factorial]
  rw [two_n_minus_n_eq_n, two_n_minus_n_plus_one_eq_n_minus_one]
  sorry
  omega
  omega


-- The rest of the proof is divided into cases n=0 and n>0, as we (may) need the h : n > 0 in the proof. For n=0
-- the proof is trivial

-- n > 0
theorem n_plus_one_divides_2n_choose_n_non_zero (n : Nat) (h : n > 0) :
n + 1 ∣ Nat.choose (2 * n) n := by
sorry

-- The main theorem
theorem n_plus_one_divides_2n_choose_n (n : Nat) :
n + 1 ∣ Nat.choose (2 * n) n := by
match n with
  | 0 =>
    omega
  | Nat.succ k =>
    apply n_plus_one_divides_2n_choose_n_non_zero (Nat.succ k)
    exact Nat.zero_lt_succ k

---------------------------------------------------
-- some additional code that we tried for 6., but did not use in the end:

-- how we figured out that the division is integer division with remainder:
#eval (λ (m : ℕ) => (m / (m + 1))) 10

-- if we managed to bring the "equality" lemma to a form with no denominators, this would complete the proof:
lemma no_denoms (n : ℕ) (h : n > 0) :
Nat.factorial (2 * n) * (n + 1) * Nat.factorial n * Nat.factorial n = n * Nat.factorial (2 * n) * Nat.factorial (n - 1) * Nat.factorial (n + 1) := by
rw [mul_comm n (Nat.factorial (2 * n))]
rw [mul_assoc, mul_assoc, ← mul_assoc (n + 1)]
rw [← Nat.factorial_succ]
rw [mul_assoc, mul_assoc, ← mul_assoc n]
rw [Nat.mul_factorial_pred]
rw [mul_comm (Nat.factorial n) (Nat.factorial (n + 1))]
apply h


-- ####################### --
-- 5. rotating isomorphism --
-- ####################### --

-- Idea: to prove the rotating isomorphism between full_binary_tree and plane_tree
-- we defined two mutually inverse functions: plane_tree_of_full_binary_tree and full_binary_tree_of_plane_tree
-- and then tried to show that composing these functions in either order results in the identity function

-- transforms full_binary_tree to plain_tree
def plane_tree_of_full_binary_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node [] -- If the full_binary_tree is a leaf, it transforms to a node with an empty list of children
| full_binary_tree.node₂ T1 T2 => -- Transforms to a plane_tree.node containing a list with the transformed versions of T1 and T2
    plane_tree.node [plane_tree_of_full_binary_tree T1, plane_tree_of_full_binary_tree T2]

-- transforms a plane_tree to a full_binary_tree
def full_binary_tree_of_plane_tree : plane_tree → full_binary_tree
| plane_tree.node [] => full_binary_tree.leaf
| plane_tree.node (left :: right :: rest) => -- A node with a list containing at least two elements in plane_tree transforms to a node₂ in full_binary_tree with the transformed left subtree and the rest of the list recursively transformed
    full_binary_tree.node₂
      (full_binary_tree_of_plane_tree left)
      (full_binary_tree_of_plane_tree (plane_tree.node (right :: rest)))
| plane_tree.node _ => full_binary_tree.leaf -- Exactly one child

-- Theorem for converting a full_binary_tree.leaf to a plane_tree.node []
theorem plane_tree_of_leaf : plane_tree_of_full_binary_tree full_binary_tree.leaf = plane_tree.node [] :=
  rfl

-- Theorem for converting a full_binary_tree.node₂ to a plane_tree.node
-- converting a full_binary_tree.node₂ results in a plane_tree.node containing a list with the converted left and right subtrees
theorem plane_tree_of_node₂ (left : full_binary_tree) (right : full_binary_tree) :
  plane_tree_of_full_binary_tree (full_binary_tree.node₂ left right) =
  plane_tree.node [plane_tree_of_full_binary_tree left, plane_tree_of_full_binary_tree right] :=
  rfl

-- Theorem for converting a plane_tree.node [] to a full_binary_tree.leaf
theorem full_binary_tree_of_leaf : full_binary_tree_of_plane_tree (plane_tree.node []) = full_binary_tree.leaf :=
  rfl

-- Theorem for converting a plane_tree.node with a list containing left and right trees
theorem full_binary_tree_of_cons (left : plane_tree) (rights : List plane_tree) :
  full_binary_tree_of_plane_tree (plane_tree.node (left :: rights)) =
    full_binary_tree.node₂
      (full_binary_tree_of_plane_tree left)
      (full_binary_tree_of_plane_tree (plane_tree.node rights)) :=
  by
    -- dsimp [full_binary_tree_of_plane_tree]
    -- match rights with
    -- | [] => rfl
    -- | [right] => rfl
    -- | right :: rest => rfl
    sorry


-- we want to show that composing functions plane_tree_of_full_binary_tree and full_binary_tree_of_plane_tree in either order results in the identity function
def rotating_iso : full_binary_tree ≃ plane_tree :=
{ toFun := plane_tree_of_full_binary_tree,
  invFun := full_binary_tree_of_plane_tree,
  left_inv := by
    intro f -- full_binary_tree_of_plane_tree (plane_tree_of_full_binary_tree f) = f
    induction f with
    | leaf => exact full_binary_tree_of_leaf
    | node₂ T1 T2 IH_T1 IH_T2 =>
      rw [plane_tree_of_node₂, full_binary_tree_of_cons]
      congr
      -- exact IH_T1
      -- exact IH_T2,
      sorry
  right_inv := by
    -- intro p -- plane_tree_of_full_binary_tree (full_binary_tree_of_plane_tree p) = p
    -- induction p with -- we got stuck with this issue but tried to prove it theoretically
    -- | node branches =>
    --   cases branches with
    --   | nil => rw [full_binary_tree_of_leaf, plane_tree_of_full_binary_tree]
    --   | cons left rights =>
    --     cases rights with
    --     | nil => rw [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree]
    --     | cons right rights =>
    --       cases rights with
    --       | nil =>
    --         rw [full_binary_tree_of_plane_tree, plane_tree_of_full_binary_tree, full_binary_tree_of_cons]
    --         simp
    --       | cons _ _ =>
    --         have h : full_binary_tree_of_plane_tree (plane_tree.node (left :: right :: rights)) =
    --           full_binary_tree.node₂ (full_binary_tree_of_plane_tree left)
    --           (full_binary_tree_of_plane_tree (plane_tree.node (right :: rights))) :=
    --             by rw [full_binary_tree_of_cons]
    --         rw [h]
             sorry }
