import Lean

syntax (name := curry) "curry" : tactic

open Lean Elab Term Meta Tactic

inductive ParamTree where
  | leaf : Expr → ParamTree
  -- Type, children
  | branch : ParamTree → ParamTree → ParamTree
deriving BEq, Repr

open ParamTree

-- Builds a tree
-- mapping input types to output types
def build_parameter_tree (e : Expr) : ParamTree :=
  match e with
    | Expr.forallE _ bty body _ =>
      branch (build_parameter_tree bty) (build_parameter_tree body)
    | val => leaf val

def find_out_ty : ParamTree → Expr
  | leaf e => e
  | branch _ body => find_out_ty body

def is_trunk : ParamTree → Bool
  | leaf _ => false
  | branch ty body => is_trunk ty ∧ is_trunk body

def find_closer (tree : ParamTree) (goal : Expr) : Option Expr :=
  -- Find a leaf whose value is the same as the goal
  match tree with
    | leaf e =>
      if e == goal then
        pure e
      else
        none
    | branch ty body =>
      find_closer ty goal
        |> Option.or $ find_closer body goal

-- Finds the lowest down branch containing a closer of the goal
def find_closer_branch (tree : ParamTree) (goal : Expr) : Option (ParamTree × Expr) :=
  -- Find a leaf whose value is the same as the goal
  match tree with
    | leaf _ =>
      none
    | branch ty body =>
      if is_trunk tree then
        (⟨tree, .⟩) <$> find_closer tree goal
      else
        (find_closer_branch ty goal).or (find_closer_branch body goal)

def maybe_curry : OptionT TacticM Unit  := do
    let goal_expr := (← getMVarDecl (← (getMainGoal))).type
    let tree := build_parameter_tree goal_expr
    let goal_leaf := find_out_ty tree
    Lean.logInfo m!"logInfo: {repr tree} {repr goal_leaf}"
    Lean.logInfo m!"logInfo: {repr (find_closer tree goal_leaf)}"
    let (trunk, closer) ← OptionT.mk (pure (find_closer_branch tree goal_leaf))
    Lean.logInfo m!"logInfo: {repr trunk} {repr closer}"

@[tactic curry]
def elab_curry : Tactic := Function.const _ $ maybe_curry >>= (Function.const _ (pure Unit.unit))

def bruh (P : Prop) (Q : Prop) : (P → Q) → P → Q := by
  curry
  sorry
