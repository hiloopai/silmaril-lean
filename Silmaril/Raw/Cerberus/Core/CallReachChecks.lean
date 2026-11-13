module

public import Silmaril.Cerberus.Core.CallReach.Defs

/-! Inhabited call and saved-return witnesses, including pointer arguments,
caller continuation retention, unknown symbols and arity errors. -/

@[expose] public section

namespace Silmaril.Cerberus.Core.CallReach.Checks

open Dynamics SeqReach

def callee : Sym := ⟨⟨[]⟩, 8530, .id "identity"⟩
def formal : Sym := ⟨⟨[]⟩, 8531, .funArgValue "p"⟩
def actual : Sym := ⟨⟨[]⟩, 8532, .id "argument"⟩
def ret : Sym := ⟨⟨[]⟩, 8533, .return_⟩
def result : Sym := ⟨⟨[]⟩, 8534, .none⟩
def intTy : Ctype := .mk [] (.basic (.integer (.signed .int)))
def pointerTy : Ctype := .mk [] (.pointer ⟨false, false, false⟩ intTy)
def wildcard : Pattern Sym := .mk [] (.base (none, .unit))
def returnValue : EE := .mk [] (.pure (.mk [] () (.sym result)))
def savedReturn : EE := .mk [] (.save (ret, .object .pointer)
  [(result, ((.object .pointer, none), .mk [] () (.val (.object (.pointer (.null intTy))))))] returnValue)
def transfer : EE := .mk [] (.run () ret [.mk [] () (.sym formal)])
def identityBody : EE := .mk [] (.sseq wildcard transfer savedReturn)

/-- The fields in order: main, calling convention, tags, std.core, impl, globals, procedures,
linkage, function metadata, loop attributes, visible objects. -/
def identityFile : Program :=
  File.mk none .normal ∅ ∅ ∅ []
    (Map.ofList [(callee, .procedure .unknown none (.object .pointer)
      [(formal, .object .pointer)] identityBody)])
    ∅ ∅ ∅ ∅

theorem identity_resolves (v : Val) :
    procedureBody identityFile callee [v] = .ok (identityBody, [(formal, v)]) := by
  apply procedure_body (loc := .unknown) (marker := none) (ty := .object .pointer)
    (params := [(formal, .object .pointer)])
  · simp [identityFile, Map.lookup]
  · simp [identityFile, Map.ofList]
  · rfl

/-- The real `run ret(p)` skips the saved return's default initializer,
binds the result, and pops only the callee frame. -/
theorem identity_body (labels : Labels) (env : Env) (v : Val)
    (caller : List Frame) (m : Mem.Concrete.State) :
    Reaches identityFile labels
      ⟨.effectExpr identityBody (env.insert formal v),
        .procedureReturn (bodyLabels identityBody) :: caller, m⟩
      ⟨.value v, caller, m⟩ := by
  refine Relation.ReflTransGen.trans (b :=
    ⟨.effectExpr transfer (env.insert formal v),
      .strongBind wildcard savedReturn (env.insert formal v) ::
        .procedureReturn (bodyLabels identityBody) :: caller, m⟩) ?_ ?_
  · apply next_reaches <;> simp [request, requestAux, awaitsScheduling, identityBody]
  · apply run_saved_value ret result (env.insert formal v) (.mk [] () (.sym formal)) v
      (pure_symbol [] formal _ v (by simp))
      [.strongBind wildcard savedReturn (env.insert formal v)] caller
      (bodyLabels identityBody) m rfl
    simp [bodyLabels, identityBody, transfer, savedReturn, returnValue, saves, Map.ofList]

def target : PE := .mk [] () (.val (.loaded (.specified (.pointer (.function callee)))))
def operand : PE := .mk [] () (.sym actual)
def metadata : PE := .mk [] () (.val (.ctype pointerTy))

/-- A call passes the actual object pointer unchanged and returns it through
the procedure's saved return label, under an arbitrary caller continuation. -/
theorem ccall_pointer (labels : Labels) (env : Env) (id addr : Int)
    (caller : List Frame) (m : Mem.Concrete.State) :
    let v : Val := .object (.pointer (.allocated id addr))
    Reaches identityFile labels
      ⟨.effectExpr (.mk [] (.ccall () metadata target [operand])) (env.insert actual v), caller, m⟩
      ⟨.value v, caller, m⟩ := by
  dsimp only
  refine (ccall_reaches [] metadata (pure_value [] _ _)
    (.cons (pure_symbol [] actual _ (.object (.pointer (.allocated id addr))) (by simp)) .nil)
    (by simp [libraryCall, identityFile, Map.ofList]) (identity_resolves _) caller m).trans ?_
  simpa [extendEnv, focusMemory] using
    identity_body labels (env.insert actual (.object (.pointer (.allocated id addr))))
      (.object (.pointer (.allocated id addr))) caller m

/-- Direct symbol calls share the same parameter and saved-return behaviour. -/
theorem proc_pointer (labels : Labels) (env : Env) (id addr : Int)
    (caller : List Frame) (m : Mem.Concrete.State) :
    let v : Val := .object (.pointer (.allocated id addr))
    Reaches identityFile labels
      ⟨.effectExpr (.mk [] (.proc () (.sym callee) [operand])) (env.insert actual v), caller, m⟩
      ⟨.value v, caller, m⟩ := by
  dsimp only
  refine (proc_reaches
    (.cons (pure_symbol [] actual _ (.object (.pointer (.allocated id addr))) (by simp)) .nil)
    (by simp [libraryCall, identityFile, Map.ofList]) (identity_resolves _) caller m).trans ?_
  simpa [extendEnv] using
    identity_body labels (env.insert actual (.object (.pointer (.allocated id addr))))
      (.object (.pointer (.allocated id addr))) caller m

/-- Arity is checked before entering the callee. -/
theorem wrong_arity : procedureBody identityFile callee [] =
    .error (.error "procedure argument count") := by
  simp [procedureBody, identityFile, Map.ofList, Map.lookup, Map.insert]; rfl

/-- Keep the dynamics' diagnostic expression, including its printer. -/
def missingError : Outcome := .error
  s!"ill-formed program: `calling an unknown procedure: Symbol({(8535 : Nat)}, SD_Id(\"{batchEscape "missing"}\"))'"

theorem missing_resolves :
    procedureBody identityFile (.mk ⟨[]⟩ 8535 (.id "missing")) [] = .error missingError :=
  unknown_procedure (file := identityFile) ⟨[]⟩ 8535 "missing" []
    (by decide +kernel) (by decide +kernel)

/-- An absent named procedure produces an error rather than a value or UB. -/
theorem unknown_call (labels : Labels) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) :
    Reaches identityFile labels
      ⟨.apply (.procedure env)
        [.loaded (.specified (.pointer (.function (.mk ⟨[]⟩ 8535 (.id "missing")))))], caller, m⟩
      ⟨.halt missingError, [], m⟩ := by
  apply dispatch_error false
  · decide +kernel
  · exact missing_resolves

/-- The same unknown-call error is reachable from source syntax. -/
theorem unknown_ccall (labels : Labels) (env : Env) (caller : List Frame)
    (m : Mem.Concrete.State) :
    Reaches identityFile labels
      ⟨.effectExpr (.mk [] (.ccall () metadata
        (.mk [] () (.val (.loaded (.specified (.pointer
          (.function (.mk ⟨[]⟩ 8535 (.id "missing")))))))) [])) env, caller, m⟩
      ⟨.halt missingError, [], m⟩ := by
  apply ccall_error [] metadata (pure_value [] _ env) .nil
  · decide +kernel
  · exact missing_resolves


end Silmaril.Cerberus.Core.CallReach.Checks
