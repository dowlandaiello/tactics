import Lean
import Mathlib.Data.Set.Defs
import Std.Data.HashMap.Basic

syntax (name := curry) "curry" : tactic

open Lean Elab Term Meta Tactic

inductive ParamTree where
  | leaf : Expr → ParamTree
  -- Type, children
  | branch : ParamTree → ParamTree → ParamTree
deriving BEq, Repr

abbrev TermMap := Std.HashMap Expr (List Expr)

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

def find_closer (tree : ParamTree) (goal : Expr) : Option $ List ParamTree :=
  -- Find a leaf whose value is the same as the goal
  match tree with
    | leaf e =>
      if e == goal then
        pure [tree]
      else
        none
    | branch ty body =>
      (tree :: .) <$> (find_closer ty goal
        |> Option.or $ find_closer body goal)

def is_closer (elem : ParamTree) (goal : Expr) : bool :=
  match elem with
    | leaf e =>
      if e == goal then
        true
      else
        false
    | _ => false

def closer_trunk : List ParamTree → Option Expr :=
  (.[0]? >>= (match . with
    | leaf e => some e
    | _ => none)) ∘ List.reverse

def maybe_curry : OptionT TacticM Unit := do
    let goal_expr := (← getMVarDecl (← (getMainGoal))).type
    let tree := build_parameter_tree goal_expr
    let goal_leaf := find_out_ty tree
    let path ← OptionT.mk (pure (find_closer tree goal_leaf))
    let trunk ← OptionT.mk (pure $ closer_trunk path)
    Lean.logInfo m!"logInfo: {repr trunk} {repr path}"

def is_lemma_closer : Expr → Bool
  | Expr.forallE _ _ _ _ => false
  | _ => true

abbrev ToVisit := List ParamTree

-- Finds the expression that closes the entire goal
-- Pops the next position to visit, checks if this closes the goal,
-- and, if it does, attempts to close this goal, too
def close (goal_leaf : Expr) : StateT ToVisit Option Expr := do
  let path ← find_closer in_tree goal_leaf
  let closer ← closer_trunk path

  if is_lemma_closer closer then
    pure closer
  else
    close (path.drop 1) closer

@[tactic curry]
def elab_curry : Tactic := Function.const _ $ maybe_curry >>= (Function.const _ (pure Unit.unit))

def bruh (P : Prop) (Q : Prop) : (P → Q) → P → Q := by
  curry
  sorry
