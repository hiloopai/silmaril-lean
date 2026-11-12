module

public import Silmaril.Cerberus.Core.Outcome.Defs

/-! Kernel checks for the arithmetic expressions reached by the exported
corpus, and for terminal labels, fuel, calls and nondeterministic choices.
Whole linked-file agreement is checked separately by the executable test driver. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics.Checks

def emptyFile : Program where
  main := none
  callingConvention := .normal
  tagDefs := ∅
  stdlib := ∅
  impl := ∅
  globs := []
  funs := ∅
  extern := ∅
  funInfo := ∅
  loopAttributes := ∅
  visibleObjects := ∅

def pe (e : PexprNode Codec.wireModel Unit Sym) : PE := .mk [] () e
def lit (n : Int) : PE := pe (.val (.object (.integer n)))
def specified (p : PE) : PE := pe (.ctor .specified [p])
def signedInt : IntegerType := .signed .int
def catchOp (op : IntOp) (x y : PE) : PE := pe (.catchExceptionalCondition signedInt op x y)

def eval (e : PE) (fuel : Nat := 128) : Observation :=
  observation (run emptyFile ∅ fuel ⟨.pureExpr e ∅, [], {}⟩).ending

/-- The exported multiply and add operations, with specified result. -/
theorem arithmetic_agrees : eval (specified (catchOp .add (lit 1)
    (catchOp .mul (lit 2) (lit 3)))) = {status := "Defined", value := some 7, specified := true} := by decide +kernel

theorem subtraction_agrees : eval (specified (catchOp .sub (lit 20) (lit 6))) =
    {status := "Defined", value := some 14, specified := true} := by decide +kernel

theorem overflow_agrees : eval (specified (catchOp .add (lit 2147483647) (lit 1))) =
    {status := "Undefined", ub := "UB036_exceptional_condition"} := by decide +kernel

/-- Concrete Core division truncates toward zero, including negative arguments. -/
theorem negative_division : eval (pe (.op .div (lit (-7)) (lit 3))) =
    {status := "Defined", value := some (-2)} := by decide +kernel

/-- Core exponentiation is integer power; zero to the zero power is one. -/
theorem exponent_zero (x : Int) : integerBin .exp x 0 = some (integer 1) := by
  simp [integerBin]

theorem exponent_negative_base : integerBin .exp (-2) 3 = some (integer (-8)) := by rfl

/-- A negative Core exponent reaches Zarith's exception rather than a C UB. -/
theorem exponent_host_exception : integerBin .exp 2 (-1) = none := by rfl

theorem bitwise_and_negative : eval (pe (.ctor .ivAnd
    [pe (.val (.ctype (.mk [] (.basic (.integer signedInt))))),lit (-7),lit (-9)])) =
    {status := "Defined", value := some (-15)} := by decide +kernel

theorem bitwise_or_negative : eval (pe (.ctor .ivOr
    [pe (.val (.ctype (.mk [] (.basic (.integer signedInt))))),lit (-7),lit (-9)])) =
    {status := "Defined", value := some (-1)} := by decide +kernel

theorem signed_conversion_wraps : eval (pe (.convInt signedInt (lit 2147483648))) =
    {status := "Defined", value := some (-2147483648)} := by decide +kernel

theorem zero_fuel : eval (lit 7) 0 = {status := "Fuel"} := by decide +kernel

theorem error_label : eval (pe (.error "test error" (lit 1))) =
    {status := "Error", reason := "test error"} := by decide +kernel

def loopSym : Sym := .mk ⟨[]⟩ 999 .none
def loopBody : PE := pe (.call (.sym loopSym) [])
def loopFile : Program := {emptyFile with stdlib := Map.ofList [(loopSym, .function .unit [] loopBody)]}

/-- A genuinely recursive pure call remains fuel exhaustion. -/
theorem recursive_call_fuel :
    observation (run loopFile ∅ 32 ⟨.pureExpr loopBody ∅, [], {}⟩).ending = {status := "Fuel"} := by decide +kernel

/-- Descriptions are not part of Cerberus symbol identity. -/
theorem symbol_description_ignored :
    (⟨⟨[1, 2, 3]⟩, 4, .id "a"⟩ : Sym).key =
      (⟨⟨[1, 2, 3]⟩, 4, .id "b"⟩ : Sym).key := rfl

/-- Simultaneous substitution keeps the first binder and shadows the outer map. -/
theorem binder_precedence :
    (extendEnv [(loopSym, integer 1), (loopSym, integer 2)]
      (Map.ofList [(loopSym, integer 3)])).lookup loopSym = some (integer 1) := by
  simp [extendEnv]

/-- A lookup through another description uses the same binding. -/
theorem environment_key_lookup :
    (Map.ofList [(loopSym, integer 7)]).lookup
      {loopSym with description := .id "different"} = some (integer 7) := by
  change (Map.ofList [(loopSym, integer 7)]).lookup loopSym = some (integer 7)
  simp [Map.ofList]

def one : Control := .value (integer 1)
def two : Control := .value (integer 2)

theorem first_choice : Respond {} (.choose [(one, []), (two, [])]) .tau ⟨one, [], {}⟩ :=
  .choose (by simp)

theorem second_choice : Respond {} (.choose [(one, []), (two, [])]) .tau ⟨two, [], {}⟩ :=
  .choose (by simp)

def memoryBody : EE := .mk [] (.action (.mk .pos
  (.mk .unknown () (.create (lit 4) (lit 4) .malloc))))

theorem memory_is_unsupported : observation (run emptyFile ∅ 8 ⟨.effectExpr memoryBody ∅, [], {}⟩).ending =
    {status := "Unsupported", reason := "Create"} := by decide +kernel

/-- Function-pointer equality uses the symbol key, ignoring its description. -/
theorem function_pointer_key_equality :
    primitive (.pointerCompare false)
      [.object (.pointer (.function loopSym)),
       .object (.pointer (.function {loopSym with description := .id "different"}))] =
    .ok .true := rfl

/-- A saved-label jump discards argument frames but retains the nearest caller boundary. -/
theorem procedure_context_boundary :
    procedureContext ∅ [.arguments .notBool [] [] ∅, .procedureReturn ∅,
      .startupEnter (.value .unit)] =
    (∅, [.procedureReturn ∅, .startupEnter (.value .unit)]) := rfl

def transferLabel : Sym := ⟨⟨[]⟩, 100, .none⟩
def transferCallee : Sym := ⟨⟨[]⟩, 101, .none⟩
def resultBody : EE := .mk [] (.pure (specified (lit 7)))
def saved : EE := .mk [] (.save (transferLabel, .loaded .integer) [] resultBody)
def jumpBody : EE := .mk [] (.run () transferLabel [])
def untakenTail : EE := .mk [] (.pure (specified (lit 99)))
def localSequence : EE := .mk [] (.sseq (.mk [] (.base (none, .tuple [.loaded .integer, .loaded .integer])))
  (.mk [] (.unseq [jumpBody, resultBody])) untakenTail)
def calleeBody : EE := .mk [] (.if_ (pe (.val .false)) saved localSequence)
def probeFile : Program := {emptyFile with
  funs := Map.ofList [(transferCallee, .procedure .unknown none (.loaded .integer) [] calleeBody)]}
def callBody : EE := .mk [] (.proc () (.sym transferCallee) [])
/-- A callee jump from an unsequenced operand discards its arena's tail. -/
theorem interleaved_callee_jump_first :
    observation (runWith 0 probeFile ∅ 128 ⟨.effectExpr callBody ∅, [], {}⟩).ending =
      {status := "Defined", value := some 7, specified := true} := by decide +kernel

/-- The other sampled schedule discards the same observable tail. -/
theorem interleaved_callee_jump_second :
    observation (runWith 1 probeFile ∅ 128 ⟨.effectExpr callBody ∅, [], {}⟩).ending =
      {status := "Defined", value := some 7, specified := true} := by decide +kernel

def nestedSequence : EE := .mk [] (.sseq (.mk [] (.base (none, .tuple [.loaded .integer, .loaded .integer])))
  (.mk [] (.unseq [.mk [] (.unseq [jumpBody, resultBody]), resultBody])) untakenTail)
def nestedCallee : EE := .mk [] (.if_ (pe (.val .false)) saved nestedSequence)
def nestedFile : Program := {probeFile with
  funs := Map.ofList [(transferCallee, .procedure .unknown none (.loaded .integer) [] nestedCallee)]}

theorem nested_callee_jump_first :
    observation (runWith 0 nestedFile ∅ 128 ⟨.effectExpr callBody ∅, [], {}⟩).ending =
      {status := "Defined", value := some 7, specified := true} := by decide +kernel

theorem nested_callee_jump_second :
    observation (runWith 1 nestedFile ∅ 128 ⟨.effectExpr callBody ∅, [], {}⟩).ending =
      {status := "Defined", value := some 7, specified := true} := by decide +kernel

/-- Struct layout lookup uses the tag key even when its description changes. -/
theorem struct_layout_description (fuel : Nat) (tags : Mem.Concrete.Tags)
    (tag : Sym) (description : SymbolDescription) :
    Mem.Concrete.typeLayout (fuel+1) tags (.mk [] (.struct {tag with description := description})) =
      Mem.Concrete.typeLayout (fuel+1) tags (.mk [] (.struct tag)) := rfl

/-- Member shifts compare identifier text and ignore diagnostic locations. -/
theorem member_shift_location (tags : Mem.Concrete.Tags) (tag : Sym)
    (name : Identifier) (location : Loc) (id addr : Int) :
    primitive (.memberShift tag {name with loc := location})
      [.object (.pointer (.allocated id addr))] tags =
    primitive (.memberShift tag name) [.object (.pointer (.allocated id addr))] tags := rfl

/-- Typed struct stores accept the same tag under a different description. -/
theorem struct_store_description (tag : Sym) (description : SymbolDescription) :
    objectMemory (.mk [] (.struct tag))
      (.struct {tag with description := description} []) = .ok (.struct_ tag []) := by
  simp [objectMemory, Mem.Concrete.symbolEq, Sym.key, Pure.pure, Except.pure]

end Silmaril.Cerberus.Core.Dynamics.Checks
