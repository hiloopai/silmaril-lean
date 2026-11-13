module

public import Silmaril.Cerberus.Core.Run.Defs
public import Silmaril.Cerberus.Core.ValuePrint.Defs
public import Silmaril.Cerberus.Codec.Undefined.Defs
public import Lean.Data.Json.Basic

/-! Oracle observations for Core. Locations are diagnostic metadata;
agreement compares defined values, output and UB names. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics

structure Observation where
  status : String
  value : Option Int := none
  specified : Bool := false
  printedValue : Option String := none
  ub : String := ""
  reason : String := ""
  stdout : String := ""
  deriving DecidableEq, Repr

def diagnosticTag : Silmaril.TaggedCodec.Tree → String
  | .atom s | .tag s _ _ => s

/-- undefined.lem:842-845,1074-1082,1092-1100. Catalogue spellings come
from the maintained codecs and Names, including parameterized UB contexts. -/
def ubName (ub : UndefinedBehaviour) : String :=
  let tag := diagnosticTag (Codec.encodeUndefinedBehaviour ub)
  match ub with
  | .DUMMY s => tag ++ "(" ++ s ++ ")"
  | .UB_std_omission ctx => tag ++ "_" ++ diagnosticTag (Codec.encodeUndefinedByOmission ctx)
  | .UB_CERB004_unspecified ctx =>
      tag ++ "__" ++ ((diagnosticTag (Codec.encodeUnspecifiedUbContext ctx)).drop 10).toString
  | .Invalid_format s => tag ++ "[" ++ s ++ "]"
  | _ => tag

def observation : Option Outcome → Observation
  | none => { status := "Fuel" }
  | some (.defined (.loaded (.specified (.integer n)))) =>
      { status := "Defined", value := some n, specified := true }
  | some (.defined (.object (.integer n))) => { status := "Defined", value := some n }
  | some (.defined v) => match valueText 256 v with
      | some text => { status := "Defined", printedValue := some text }
      | none => { status := "Unsupported", reason := "exit value outside printable fragment" }
  | some (.ub _ ub) => { status := "Undefined", ub := ubName ub }
  | some (.error why) => { status := "Error", reason := why }
  | some (.unsupported why) => { status := "Unsupported", reason := why }
  | some .aborted => { status := "Aborted" }

/-- The driver keeps output alongside the terminal value, driver.lem:245-256.
Fuel retains the output accumulated by the resumable final state. -/
def runObservation {file : Program} {labels : Labels} {start : State}
    (r : Run file labels start) : Observation :=
  {observation r.ending with stdout := r.finalState.memory.stdout}

def Observation.json (o : Observation) : Lean.Json :=
  Lean.Json.mkObj [("status", .str o.status), ("details", Lean.Json.mkObj (
    [("stdout", .str (if o.status == "Defined" then batchEscape o.stdout else "")), ("stderr", .str "")] ++
    (if o.status == "Defined" then [("value", .str (o.printedValue.getD (if o.specified then s!"Specified({o.value.getD 0})" else s!"{o.value.getD 0}")))]
     else if o.status == "Undefined" then [("ub", .str o.ub)]
     else [("reason", .str o.reason)])))]

end Silmaril.Cerberus.Core.Dynamics
