import Hammer
import Mathlib.Tactic.MkIffOfInductiveProp
import Lean.Expr

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true

inductive A : Type

@[mk_iff]
inductive B : A -> Prop where
  | b x : B x 

#check B.b

#check 0

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
      --let cnstExpr := cnst.toExpr
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
        && !cnstInfo.name.toString.contains "LLVM" 
        && !cnstInfo.name.toString.contains "BitVec" 
        && !cnstInfo.name.toString.contains "IO" 
        && !cnstInfo.name.toString.contains "Lean" then 
        match cnstInfo with
          | Lean.ConstantInfo.inductInfo inductVal => 
            let ctors := inductVal.ctors
            let ctorsTypes := ctors.map (fun ctor ↦ 
              match (Lean.Environment.find? env ctor) with
                | some val => (Lean.ConstantInfo.toConstantVal val).type
                | none => cnstInfo.type)
            indCtors := ctorsTypes ++ indCtors
            dbg_trace f!"+ local cnst: {cnstName} with constructors: {ctorsTypes}"
          | _ => return
      if max > 10000 then
        return

      return 

def inductive_definitions : List Lean.Expr :=
    let constants := Lean.Environment.constants >> Lean.MonadEnv.getEnv
    let rec cnstToIndDefs  (defsAcc : List Lean.Expr) (remainingCnsts : List (Int × Lean.ConstantInfo)) : (List Lean.Expr) :=
      match remainingCnsts with
        | [] => defsAcc
        | (_, cnstInfo) :: cnstsRest =>
          match cnstInfo with 
            | Lean.ConstantInfo.inductInfo inductVal => 
              let ctors := inductVal.ctors
              let ctorsTypes := (fun env ↦ 
                (List.filterMap (fun ctor ↦
                  match Lean.Environment.find? env ctor with
                    | some val => some (Lean.ConstantInfo.toConstantVal val).type
                    | none => none) ctors ) ) >> Lean.MonadEnv.getEnv
              cnstToIndDefs (ctorsTypes ++ defsAcc) cnstsRest
            | _ => (cnstToIndDefs defsAcc cnstsRest)

    cnstToIndDefs [] >> constants

example : forall x: A, B x := by
  --have h':(forall x: A, B x) := by apply B.b
  --duper [*]
  --auto [*]
  --hammer {disableAesop := false, preprocessing := aesop}
  --hammer
  --aesop
  --hammer [b_iff] {autoPremises := 8}
  list_local_decls
  list_constants
  hammer {autoPremises := 8}
