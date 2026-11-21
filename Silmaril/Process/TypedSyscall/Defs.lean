module

/-! A POSIX-style user/kernel boundary. Names, ABI reification, image layout,
memory semantics, and scheduling policy belong to its fillings. -/

@[expose] public section

namespace Silmaril.Process.TypedSyscall

structure Signature where
  Request : Type
  Response : Request → Type

/-- Translate requests forward and project answers back at the corresponding
request index. A lossy projection is allowed; it is not an inverse ABI encoding. -/
structure Signature.Hom (source target : Signature) where
  request : source.Request → target.Request
  response : (req : source.Request) → target.Response (request req) → source.Response req

def Signature.Hom.id (sig : Signature) : sig.Hom sig := ⟨fun req => req, fun _ reply => reply⟩

def Signature.Hom.then {source middle target : Signature}
    (first : source.Hom middle) (second : middle.Hom target) : source.Hom target :=
  ⟨fun req => second.request (first.request req),
    fun req reply => first.response req (second.response (first.request req) reply)⟩

/-- The CPU supplies a continuation exactly for replies that return to user mode. -/
inductive Action (sig : Signature) (Core Store Stop : Type) where
  | retire (core : Core) (store : Store)
  | call (req : sig.Request) (resume : sig.Response req → Core)
  | stop (reason : Stop)

def Action.push {source target : Signature} {Core Store Stop : Type} (hom : source.Hom target) :
    Action source Core Store Stop → Action target Core Store Stop
  | .retire core store => .retire core store
  | .stop reason => .stop reason
  | .call req resume => .call (hom.request req) fun reply => resume (hom.response req reply)

inductive Completion (Reply Store : Type) where
  | returned (reply : Reply) (store : Store)
  | exited (status : Nat) (store : Store)

def Completion.map {Reply Other Store : Type} (project : Reply → Other) :
    Completion Reply Store → Completion Other Store
  | .returned reply store => .returned (project reply) store
  | .exited status store => .exited status store

/-- One completed syscall; an absent completion is not a reply or an exit. -/
abbrev Kernel (sig : Signature) (Store Event : Type) :=
  (req : sig.Request) → Store → Event → Completion (sig.Response req) Store → Prop

def Kernel.pull {source target : Signature} {Store Event : Type}
    (hom : source.Hom target) (kernel : Kernel target Store Event) : Kernel source Store Event :=
  fun req store event answer => ∃ concrete, kernel (hom.request req) store event concrete ∧
    concrete.map (hom.response req) = answer

abbrev Cpu (sig : Signature) (Image Core Store Stop : Type) := Image → Core → Store → Action sig Core Store Stop

def Cpu.push {source target : Signature} {Image Core Store Stop : Type}
    (hom : source.Hom target) (cpu : Cpu source Image Core Store Stop) :
    Cpu target Image Core Store Stop := fun image core store => (cpu image core store).push hom

/-- Choose one core and a function for replacing its slot. `none` means this policy
did not select a core, not that every core has terminated. -/
abbrev Scheduler (Pool Core : Type) := Pool → Option (Core × (Core → Pool))

def Scheduler.single (Core : Type) : Scheduler Core Core := fun core => some (core, id)

inductive Outcome (Pool Store Stop : Type) where
  | running (pool : Pool) (store : Store)
  | exited (status : Nat) (store : Store)
  | stopped (reason : Stop)
  | idle

def Completion.finish {Reply Pool Store Stop : Type} (commit : Reply → Pool) :
    Completion Reply Store → Outcome Pool Store Stop
  | .returned reply store => .running (commit reply) store
  | .exited status store => .exited status store

/-- One selected user step or completed kernel call. `Store` is supplied by the
memory/environment filling; `Image` is the CPU's immutable image parameter. -/
def Step {sig : Signature} {Image Pool Core Store Event Stop : Type}
    (cpu : Cpu sig Image Core Store Stop) (kernel : Kernel sig Store Event)
    (schedule : Scheduler Pool Core) (image : Image) (pool : Pool) (store : Store)
    (observation : Option Event) (outcome : Outcome Pool Store Stop) : Prop :=
  match schedule pool with
  | none => observation = none ∧ outcome = .idle
  | some (core, replace) =>
    match cpu image core store with
    | .retire next updated => observation = none ∧ outcome = .running (replace next) updated
    | .stop reason => observation = none ∧ outcome = .stopped reason
    | .call req resume => ∃ event answer, kernel req store event answer ∧
        observation = some event ∧ outcome = answer.finish (fun reply => replace (resume reply))

end Silmaril.Process.TypedSyscall
