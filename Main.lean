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
  -- because of MonadLift, IO monad also available
  let _c ← (pure: _ → IO _) Lean.Syntax.missing
  let _a ← liftIO do
      IO.println "a"
      let _b := 12
      (pure: _) Lean.Syntax.missing
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

def divide (x :Float ) (y :Float):ExceptT String Id Float :=
  if y ==0 then
    throw "can't divide by zero"
  else
    pure (x /y)
#eval divide 8 0

def lt (x : Except String Float):
  StateT Nat (Except String) Float := (monadLift : _) x

#print lt
