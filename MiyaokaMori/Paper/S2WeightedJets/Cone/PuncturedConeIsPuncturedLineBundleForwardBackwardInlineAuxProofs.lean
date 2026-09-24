import MiyaokaMori.Prelude

/-! # `inline_aux_proofs`: undo `abstractNestedProofs` in a hypothesis or in the goal

When a definition is compiled, Lean abstracts the proofs nested in its body (typically instance proofs
of `Prop`-valued classes such as `HasPullback`, `IsLocallyFree`, `HasWeakSheafify`) into auxiliary
lemmas `foo._proof_k`. A hypothesis obtained by unfolding such a definition (e.g. `obtain ⟨h1, h2⟩ := hβ`
for `hβ : IsTotalSpaceToConeHom …`) therefore contains `foo._proof_k args`, whereas the same statement
elaborated afresh contains the instance terms themselves. The two are definitionally equal only through
proof irrelevance at dozens of nested sites, and `Meta.isDefEq` / the kernel spend 5–30 s on it.
`inline_aux_proofs at h` replaces every
`foo._proof_k args` in the type of `h` by the instantiated body, making it syntactically identical to
a fresh elaboration; `inline_aux_proofs` does the same for the goal. The change of type is recorded
with `replaceLocalDeclDefEq` / `replaceTargetDefEq` (no defeq check by the elaborator).
-/

open Lean Meta Elab Tactic

/-- Replace applications of auxiliary `_proof_…` lemmas by their instantiated bodies (recursively). -/
partial def Lean.Expr.inlineAuxProofs (env : Environment) (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub.getAppFn with
    | .const n us =>
      match n with
      | .str _ s =>
        if s.startsWith "_proof_" then
          match env.find? n with
          | some (.thmInfo info) =>
            some (inlineAuxProofs env ((info.value.instantiateLevelParams info.levelParams us).beta sub.getAppArgs))
          | _ => none
        else none
      | _ => none
    | _ => none

/-- `inline_aux_proofs at h`: inline auxiliary `_proof_…` lemmas in the type of `h`. -/
elab "inline_aux_proofs" "at" h:ident : tactic => withMainContext do
  let fvarId ← getFVarId h
  let t ← instantiateMVars (← inferType (.fvar fvarId))
  let t' := t.inlineAuxProofs (← getEnv)
  let g ← getMainGoal
  let g' ← g.replaceLocalDeclDefEq fvarId t'
  replaceMainGoal [g']

/-- `inline_aux_proofs`: inline auxiliary `_proof_…` lemmas in the goal. -/
elab "inline_aux_proofs" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' := t.inlineAuxProofs (← getEnv)
  let g' ← g.replaceTargetDefEq t'
  replaceMainGoal [g']
