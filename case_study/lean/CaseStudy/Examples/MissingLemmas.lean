import Hammer
import Mathlib.Tactic.MkIffOfInductiveProp
import Lean.Expr

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true

inductive A : Type

@[mk_iff]
inductive B : A -> Prop where
  | b x : B x

#check B.b

--def test := do
--  let lctx ← Lean.MonadLCtx.getLCtx
--  lctx.forM fun elem: Lean.LocalDecl => do
--    let elemExpr := elem.toExpr
--    dbg_trace f!"local declaration: {elemExpr}"

elab "list_local_decls" : tactic => do
    let ctx ← Lean.MonadLCtx.getLCtx -- get the local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr -- Find the expression of the declaration.
      let declName := decl.userName -- Find the name of the declaration.
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr}"

elab "list_constants" : tactic => do
    let env ← Lean.MonadEnv.getEnv -- get the local environment
    let constants := env.constants -- get the local constants.
    let mut max := 0
    let mut indCtors : List Lean.Expr := []
    for cnst in constants do
      max := max + 0
      let (cnstName, cnstInfo) := cnst
      if cnstInfo.isInductive && !cnstInfo.name.isInternal
        && !cnstInfo.name.toString.contains "Auto"
        && !cnstInfo.name.toString.contains "Aesop"
        && !cnstInfo.name.toString.contains "Batteries"
        && !cnstInfo.name.toString.contains "Std"
        && !cnstInfo.name.toString.contains "Duper"
        && !cnstInfo.name.toString.contains "System"
        && !cnstInfo.name.toString.contains "Hammer"
        --&& !cnstInfo.name.toString.contains "LLVM"
        --&& !cnstInfo.name.toString.contains "BitVec"
        --&& !cnstInfo.name.toString.contains "IO"
        && !cnstInfo.name.toString.contains "Lean" then
        match cnstInfo with
          | Lean.ConstantInfo.inductInfo inductVal =>
            let ctors := inductVal.ctors
            let ctorsTypes := ctors.map (fun ctor ↦
              match (Lean.Environment.find? env ctor) with
                | some val => (Lean.ConstantInfo.toConstantVal val).type
                | none => cnstInfo.type)
            indCtors := ctorsTypes ++ indCtors
            dbg_trace "+ local cnst: {cnstName} with constructors: {ctorsTypes}"
          | _ => return
      if max > 10000 then
        return

open Lean in
def inductive_definitions : CoreM (List Expr) := do
    let env ← MonadEnv.getEnv
    let constants := Environment.constants env
    let cnstToIndDefs (defsAcc: List Expr) _ (nextCnstInfo: ConstantInfo): (List Expr) :=
        match nextCnstInfo with
          | ConstantInfo.inductInfo inductVal =>
            let ctors := inductVal.ctors
            let ctorsTypes := (List.filterMap (fun ctor ↦
                match Environment.find? env ctor with
                  | some val => some (ConstantInfo.toConstantVal val).type
                  | none => none) ctors )
            (ctorsTypes ++ defsAcc)
          | _ => defsAcc
    return SMap.fold cnstToIndDefs [] constants

example : forall x: A, B x := by
  --have h':(forall x: A, B x) := by apply B.b
  --have h': forall (x : A), B x := by apply B.b
  --duper [*]
  --auto [*]
  --hammer {disableAesop := false, preprocessing := aesop}
  --hammer
  --aesop
  --hammer [b_iff] {autoPremises := 8}
  list_local_decls

  list_constants
  sorry
  -- hammer {autoPremises := 8}
