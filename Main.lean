import LeanForeign.S
import Lean
def main : IO Unit := do
  IO.println (mkS 10 20 "hello").addXY
  IO.println (mkS 10 20 "hello").string
  appendToGlobalS "foo"
  appendToGlobalS "bla"
  getGlobalString >>= IO.println
  updateGlobalS (mkS 0 0 "world")
  getGlobalString >>= IO.println
  pure ()

open Lean Elab Command Term Meta

-- syntax (name := mc1) "#mc1" : command
-- @[commandElab mc1]
-- def mc1Impl : CommandElab

elab "#findCElab " c:command : command => do
  let macroRes ← liftMacroM <| expandMacroImpl? (←getEnv) c
  match macroRes with
  | some (name, _) => logInfo s!"Next step is a macro: {name.toString}"
  | none =>
    let kind := c.raw.getKind
    let elabs := commandElabAttribute.getEntries (←getEnv) kind
    match elabs with
    | [] => logInfo s!"There is no elaborators for your syntax, lools like its bad"
    | _ => logInfo s!"your syntx may be elaborated by: {elabs.map (fun el => el.declName.toString)}"

#findCElab def lala := 12
#findCElab example : 1 = 1 := rfl
