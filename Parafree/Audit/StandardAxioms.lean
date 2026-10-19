import Lean.Elab.Command
import Lean.ResolveName
import Lean.Util.CollectAxioms

/-! Audits include declaration types and bodies, sharing one dependency traversal.
Module-based selection also covers private helpers and compatibility ports whose
namespaces differ from their source module. -/
namespace Parafree.Audit
open Lean Elab Command

private def checkAxioms (names : Array Name) (scope : String := "") : CommandElabM Unit := do
  if names.isEmpty then
    throwError "An axiom audit must select at least one declaration"
  let env ← getEnv
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  for axiomName in state.axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "The audited declarations depend on the nonstandard axiom {axiomName}"
  logInfo m!"Axiom audit passed: {names.size} declarations{scope}; axioms: {state.axioms}"

elab "#assert_standard_axioms " "[" decls:ident,* "]" : command => do
  let names ← decls.getElems.mapM fun decl =>
    liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
  checkAxioms names

/-- Check every declaration originating in the selected imported modules.
Exclusions apply to source modules, never to dependencies of selected results. -/
elab "#assert_module_standard_axioms " modulePrefix:ident " excluding " "[" excluded:ident,* "]" : command => do
  let env ← getEnv
  let exclusions := excluded.getElems.map (·.getId)
  let selected := fun (m : Name) => modulePrefix.getId.isPrefixOf m &&
    !exclusions.any (fun e => e.isPrefixOf m)
  let modules := env.header.moduleNames
  let selectedModules := modules.map selected
  let selectedMain := selected env.header.mainModule
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc name _ =>
    let included :=  match env.getModuleIdxFor? name with
      | some i => selectedModules[i.toNat]!
      | none => selectedMain
    if included then acc.push name else acc
  checkAxioms (names.qsort Name.quickLt)
    s!" in {(selectedModules.filter id).size} imported modules"

end Parafree.Audit
