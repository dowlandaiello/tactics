import Lean
import Std.Data.HashMap.Basic

open Lean Elab Term Meta Tactic

syntax (name := curry) "curry" : tactic

structure ParamGraph where
  types   : List $ Expr × (Option Expr)
  names   : Std.HashMap Expr Name
  built_e : List Expr

def insert_ty (e : Expr) : StateM ParamGraph Expr := do
  -- Note: will need bname later for actually creating the expression
  match e with
    -- α → β
    -- α = bty β = body
    | Expr.forallE _ bty body _ =>
      let child ← insert_ty body
      modify λs => ⟨⟨bty, some child⟩ :: s.types, s.names, s.built_e⟩

      pure bty
    | e =>
      modify λs => ⟨⟨e, none⟩ :: s.types, s.names, s.built_e⟩

      pure e

def insert_bvar (name : Name) (ty : Expr) : StateM ParamGraph Unit := do
 modify λs => ⟨s.types, s.names.insert ty name, s.built_e⟩

def close (e : Expr) : OptionT (StateM ParamGraph) (List Expr) := do
  -- A node can close this "goal" if it produces the entire goal type
  -- as an output
  --
  -- There must be at least one goal like this
  let ⟨in_ty, _⟩ ← liftOption <| ((← get).types.filter ((. == some e) ∘ Prod.snd))[0]?

  -- We can attempt to close the input goal to form a big expression
  pure $ (← close in_ty) ++ [e]

def maybe_curry : OptionT TacticM Unit := do
    let goal_expr := (← getMVarDecl (← (getMainGoal))).type

    let s : ParamGraph := ⟨⟨Std.DHashMap.ofList []⟩, ⟨Std.DHashMap.ofList []⟩, []⟩
    let ⟨_, g⟩ := (insert goal_expr).run s

    sorry

@[tactic curry]
def elab_curry : Tactic := Function.const _ $ maybe_curry >>= (Function.const _ (pure Unit.unit))
