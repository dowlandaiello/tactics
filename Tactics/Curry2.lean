import Lean
import Std.Data.HashMap.Basic
import Mathlib.Tactic

open Lean Elab Term Meta Tactic

syntax (name := curry) "curry" : tactic

structure ParamGraph where
  types   : List $ Expr × (Option Expr)
  names   : Std.HashMap Expr Name
deriving Repr

def insert_ty (e : Expr) : StateM ParamGraph Expr := do
  -- Note: will need bname later for actually creating the expression
  match e with
    -- α → β
    -- α = bty β = body
    | Expr.forallE _ bty body _ =>
      let child ← insert_ty body
      modify λs => ⟨⟨bty, some child⟩ :: s.types, s.names⟩

      pure bty
    | e =>
      modify λs => ⟨⟨e, none⟩ :: s.types, s.names⟩

      pure e

def insert_bvar (name : Name) (ty : Expr) : StateM ParamGraph Unit := do
 modify λs => ⟨s.types, s.names.insert ty name⟩

partial def close (e : Expr) : OptionT (StateM ParamGraph) (List Expr) := do
    -- A node can close this "goal" if it produces the entire goal type
    -- as an output
    --
    -- There must be at least one goal like this
    let ⟨in_ty, _⟩ ← OptionT.mk <| pure ((. == some e) ∘ Prod.snd |> (← get).types.filter)[0]?
    modify (λs => { s with types := (. != some e) ∘ Prod.snd |> s.types.filter })

    close in_ty

partial def maybe_curry : OptionT (StateT ParamGraph TacticM) Unit := do
    let goal_expr := (← getMVarDecl (← (getMainGoal))).type
    let lctx ← getLCtx

    lctx.fvarIdToDecl.toList.filter id

    modify (λs => s |> Prod.snd ∘ (insert_ty goal_expr).run)

    Lean.logInfo m!"logInfo: {repr (← get)}"
    let out_expr ← modifyGet (λs => (close goal_expr).run s)
    Lean.logInfo m!"logInfo: {out_expr}"

@[tactic curry]
def elab_curry : Tactic := Function.const _ $ (((StateT.run . ⟨[], ⟨Std.DHashMap.ofList []⟩⟩) ∘ OptionT.run) <| maybe_curry) >>= (Function.const _ (pure Unit.unit))

def my_proof (P : Prop) (Q : Prop) : (P → Q) → P → Q := by
  curry
