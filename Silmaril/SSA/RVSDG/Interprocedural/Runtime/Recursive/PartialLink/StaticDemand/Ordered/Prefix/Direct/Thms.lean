module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct.Sources

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct

open Continuation.Partial.Executable (Actions)
open Isomorphism.RecursiveCall.Numbered (linkedLambda)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {table : MemberSummaries V S} {imports : Ports (Ty V S)} {scope : Scope m}
variable {fn : Function V S}
variable {inputsL inputsR : Tuple m.Val imports}

theorem widen_read {args users head : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (wires : Wires args past users) (inputs : Tuple m.Val args) (locals : Locals m.Val past)
    (value : Tuple m.Val head) :
    (widen wires).read inputs (locals.snoc value) = wires.read inputs locals :=
  Proofs.widen_read wires inputs locals value

theorem seed_selects (family : StaticDemand.Family Op table imports) (i : Fin table.members.length)
    (inputs : Tuple m.Val imports) (origins : Wires imports [memberPorts table.members] (table.at i).captures)
    (found : phiCaptures family i = some origins) :
    let seeded := Scope.seed family inputs inputs
    selects seeded.guardL i ((seedWires i origins).read inputs seeded.localsL) :=
  Proofs.seed_selects family i inputs origins found

theorem new_selects (binding : Binding Op scope.table imports scope.past fn)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table) :
    selects (binding.extendGuard guard inputs locals) (0 : Fin (scope.table.members.length + 1))
      ((newWires binding).read inputs (locals.snoc (.cons (binding.value inputs locals) .nil))) :=
  Proofs.new_selects binding inputs locals guard

theorem capture_reads {F : Ty V S → Type w} {context params : Ports (Ty V S)}
    {past : List (Ports (Ty V S))} (wires : Wires imports past context)
    (inputs : Tuple F imports) (locals : Locals F past) (args : Tuple F params) :
    Boundary.Reads (captureBoundary wires) inputs locals (prependContext args (wires.read inputs locals)) :=
  Proofs.capture_reads wires inputs locals args

theorem forward_reads {F : Ty V S → Type w} {entry child : Ports (Ty V S)}
    {outer past : List (Ports (Ty V S))} (source : Boundary imports entry outer) (wires : Wires entry past child)
    (inputs : Tuple F imports) (locals : Locals F outer) (values : Tuple F entry)
    (reads : Boundary.Reads source inputs locals values) (childLocals : Locals F past) :
    Boundary.Reads (Boundary.forward source wires) inputs locals (wires.read values childLocals) :=
  Proofs.forward_reads source wires inputs locals values reads childLocals

theorem feedback_initial {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) (current : Tuple m.Val carried)
    (reads : source.Reads inputs locals current) : (source.feedback body).Reads inputs locals current :=
  Proofs.feedback_initial source body inputs locals current reads

theorem feedback_preserves {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) (current next : Tuple m.Val carried)
    (reads : (source.feedback body).Reads inputs locals current) (stable : body.Stable current next) :
    (source.feedback body).Reads inputs locals next :=
  Proofs.feedback_preserves source body inputs locals current next reads stable

/-- A returned body packet preserves the tracked origins on the next
activation, by the actual result wires. The decision is independent. -/
theorem feedback_return_reads {carried : Ports (Ty V S)} {outer sigs : List (Ports (Ty V S))}
    {member : Option (MemberSummaries V S)} (source : Boundary imports carried outer)
    (body : Code Op carried [] sigs (Theta.BodyResults carried) true member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) {current next : Tuple m.Val carried}
    {decision : m.Val (.control 2)} (reads : (source.feedback body).Reads inputs locals current)
    (returned : body.Forwards current (.cons decision next)) : (source.feedback body).Reads inputs locals next :=
  feedback_preserves source body inputs locals current next reads (fun p passes => returned (.tail p) p passes)

theorem start_reads {entry : Ports (Ty V S)} {outer past : List (Ports (Ty V S))}
    (source : Boundary imports entry outer) (inputs : Tuple m.Val imports) (outerLocals : Locals m.Val outer)
    (values : Tuple m.Val entry) (locals : Locals m.Val past)
    (reads : source.Reads inputs outerLocals values) :
    (ScopeBoundary.start source past).Reads inputs outerLocals values locals :=
  Proofs.start_reads source inputs outerLocals values locals reads

theorem enter_reads {entry child : Ports (Ty V S)} {outer past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry outer past) (wires : Wires entry past child)
    (inputs : Tuple m.Val imports) (outerLocals : Locals m.Val outer)
    (values : Tuple m.Val entry) (locals : Locals m.Val past) (reads : source.Reads inputs outerLocals values locals) :
    (source.enter wires).Reads inputs outerLocals (wires.read values locals) :=
  Proofs.enter_reads source wires inputs outerLocals values locals reads

theorem snoc_reads {entry out : Ports (Ty V S)} {outer past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry outer past) (outMap : Boundary imports out outer)
    (inputs : Tuple m.Val imports) (outerLocals : Locals m.Val outer) (values : Tuple m.Val entry)
    (locals : Locals m.Val past) (result : Tuple m.Val out)
    (reads : source.Reads inputs outerLocals values locals) (added : outMap.Reads inputs outerLocals result) :
    (source.snoc outMap).Reads inputs outerLocals values (locals.snoc result) :=
  Proofs.snoc_reads source outMap inputs outerLocals values locals result reads added

theorem join_reads {child out : Ports (Ty V S)} {outer : List (Ports (Ty V S))}
    {loops : Bool} {member : Option (MemberSummaries V S)} {extra : Nat}
    {armSigs : Fin (extra + 2) → List (Ports (Ty V S))} (source : Boundary imports child outer)
    (arms : (i : Fin (extra + 2)) → Code Op child [] (armSigs i) out loops member)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val outer) (values : Tuple m.Val child)
    (result : Tuple m.Val out) (i : Fin (extra + 2))
    (reads : source.Reads inputs locals values) (returned : (arms i).Forwards values result) :
    (source.join arms).Reads inputs locals result :=
  Proofs.join_reads source arms inputs locals values result i reads returned

theorem scoped_call {entry : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry scope.past past) (i : Fin scope.table.members.length)
    (target : Origin entry past (scope.table.at i).fn.port) (witnesses : Wires entry past (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : source.project (.cons target witnesses) = some sources) (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (outerLocals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs outerLocals)) (values : Tuple m.Val entry)
    (locals : Locals m.Val past) (reads : source.Reads inputs outerLocals values locals) :
    guard i ((Wires.read (.cons target .nil) values locals).get .head) (witnesses.read values locals) :=
  Proofs.scoped_call source i target witnesses sources expected found same inputs outerLocals guard resolved values locals reads

theorem forget_result {entry out : Ports (Ty V S)} {outer past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry outer past) (inputs : Tuple m.Val imports) (outerLocals : Locals m.Val outer)
    (values : Tuple m.Val entry) (locals : Locals m.Val past) (result : Tuple m.Val out)
    (reads : source.Reads inputs outerLocals values locals) :
    (source.snoc ⟨fun _ => none⟩).Reads inputs outerLocals values (locals.snoc result) :=
  snoc_reads source _ inputs outerLocals values locals result reads (by intro _ _ _ found; cases found)

theorem boundary_call {entry : Ports (Ty V S)} (source : Boundary imports entry scope.past)
    (i : Fin scope.table.members.length)
    (target : Port entry (scope.table.at i).fn.port)
    (witnesses : Wires entry [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : Boundary.project source (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (values : Tuple m.Val entry)
    (reads : Boundary.Reads source inputs locals values) :
    guard i (values.get target) (witnesses.read values PUnit.unit) :=
  Proofs.boundary_call source i target witnesses sources expected found same inputs locals guard resolved values reads

theorem projected_call {context params : Ports (Ty V S)} (captures : Wires imports scope.past context)
    (i : Fin scope.table.members.length)
    (target : Port (context ++ params) (scope.table.at i).fn.port)
    (witnesses : Wires (context ++ params) [] (scope.table.at i).captures)
    (sources expected : Wires imports scope.past (CallPorts scope.table i))
    (found : project captures (.cons (.arg target) witnesses) = some sources)
    (same : sources.addresses = expected.addresses)
    (inputs : Tuple m.Val imports) (locals : Locals m.Val scope.past) (guard : Guard m scope.table)
    (resolved : selects guard i (expected.read inputs locals)) (args : Tuple m.Val params) :
    let entry := prependContext args (captures.read inputs locals)
    guard i (entry.get target) (witnesses.read entry PUnit.unit) :=
  boundary_call (captureBoundary captures) i target witnesses sources expected found same inputs locals guard resolved _
    (capture_reads captures inputs locals args)

@[expose] def Routes.seed (family : StaticDemand.Family Op table imports) (inputsL inputsR : Tuple m.Val imports) :
    Routes inputsL inputsR (Scope.seed family inputsL inputsR) :=
  fun i =>
    match found : phiCaptures family i with
    | none => none
    | some captures =>
      some ⟨seedWires i captures,
        seed_selects family i inputsL captures found, seed_selects family i inputsR captures found⟩

@[expose] def Routes.add (routes : Routes inputsL inputsR scope)
    (binding : Binding Op scope.table imports scope.past fn) :
    Routes inputsL inputsR (scope.add binding inputsL inputsR) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact some ⟨newWires binding,
      new_selects binding inputsL scope.localsL scope.guardL, new_selects binding inputsR scope.localsR scope.guardR⟩
  · exact (routes j).map fun route =>
      ⟨widen route.wires,
        (widen_read route.wires inputsL scope.localsL (.cons (binding.value inputsL scope.localsL) .nil)).symm ▸ route.left,
        (widen_read route.wires inputsR scope.localsR (.cons (binding.value inputsR scope.localsR) .nil)).symm ▸ route.right⟩

@[expose] def Routes.skip (routes : Routes inputsL inputsR scope)
    (definition : LambdaTerm Op imports scope.past fn) :
    Routes inputsL inputsR (scope.skip definition inputsL inputsR) := fun i =>
  (routes i).map fun route =>
    ⟨widen route.wires,
      (widen_read route.wires inputsL scope.localsL
        (.cons (linkedLambda definition.toGraph inputsL scope.localsL) .nil)).symm ▸ route.left,
      (widen_read route.wires inputsR scope.localsR
        (.cons (linkedLambda definition.toGraph inputsR scope.localsR) .nil)).symm ▸ route.right⟩

section Check

variable {context : Ports (Ty V S)} {actions : Actions m σ}

@[expose] def resolved {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (captures : Wires imports scope.past context)
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table))
    (inputsL inputsR : Tuple m.Val imports) : Prop :=
  (∀ args, code.ResolvedWith scope.guardL (prependContext args (captures.read inputsL scope.localsL))) ∧
  (∀ args, code.ResolvedWith scope.guardR (prependContext args (captures.read inputsR scope.localsR)))

/-- Resolution for all activations satisfying the boundary map, separately
for each checked link. Untracked ports may have arbitrary runtime values. -/
@[expose] def resolvedAt {entry outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
    {loops : Bool} {member : Option (MemberSummaries V S)} (source : ScopeBoundary imports entry scope.past past)
    (code : Code Op entry past sigs outs loops member) (known : some scope.table = member)
    (inputsL inputsR : Tuple m.Val imports) : Prop :=
  (∀ values locals, source.Reads inputsL scope.localsL values locals → code.ResolvedAt (known ▸ scope.guardL) values locals) ∧
  (∀ values locals, source.Reads inputsR scope.localsR values locals → code.ResolvedAt (known ▸ scope.guardR) values locals)

/-- Collect a certificate for each typed arm at its actual finite index. -/
@[expose] def collectArms : (n : Nat) → {P : Fin n → Prop} →
    ((i : Fin n) → Option (PLift (P i))) → Option (PLift (∀ i, P i))
  | 0, _, _ => some ⟨fun i => i.elim0⟩
  | n + 1, _, check => do
    let head ← check 0
    let tail ← collectArms n (fun i => check i.succ)
    pure ⟨Fin.cases head.down tail.down⟩

/-- A proof-producing check on the actual projected target and witness wires. -/
abbrev SourceResolver (inputsL inputsR : Tuple m.Val imports) (scope : Scope m) :=
  (i : Fin scope.table.members.length) → (sources : Wires imports scope.past (CallPorts scope.table i)) →
    Option (PLift (selects scope.guardL i (sources.read inputsL scope.localsL) ∧
      selects scope.guardR i (sources.read inputsR scope.localsR)))

@[expose] def routeSources (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope) :
    SourceResolver inputsL inputsR scope := fun i sources =>
  match routes i with
  | none => none
  | some route =>
    if same : sources.addresses = route.wires.addresses then
      let origin := sources.get .head
      if (checked.state.left.available (entry := inputsL) Known.ordinary origin).isSome &&
          (checked.state.right.available (entry := inputsR) Known.ordinary origin).isSome then
        let equal := NestedTheta.Equality.addresses_injective sources route.wires same
        some ⟨equal.symm ▸ route.left, equal.symm ▸ route.right⟩
      else none
    else none

@[expose] def resolveSiteWith (resolve : SourceResolver inputsL inputsR scope)
    {entry : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry scope.past past)
    {called : MemberSummaries V S} (known : some scope.table = some called)
    (i : Fin called.members.length) (target : Origin entry past (called.at i).fn.port)
    (witnesses : Wires entry past (called.at i).captures) :
    Option (PLift
      ((∀ values locals, source.Reads inputsL scope.localsL values locals →
          (known ▸ scope.guardL : MemberResolution m (some called)) i
            ((Wires.read (.cons target .nil) values locals).get .head) (witnesses.read values locals)) ∧
       (∀ values locals, source.Reads inputsR scope.localsR values locals →
          (known ▸ scope.guardR : MemberResolution m (some called)) i
            ((Wires.read (.cons target .nil) values locals).get .head) (witnesses.read values locals)))) := by
  obtain rfl := Option.some.inj known
  exact match found : source.project (.cons target witnesses) with
  | none => none
  | some sources => (resolve i sources).map fun ready =>
    ⟨fun values locals reads => scoped_call source i target witnesses sources sources found rfl
      inputsL scope.localsL scope.guardL ready.down.1 values locals reads,
      fun values locals reads => scoped_call source i target witnesses sources sources found rfl
        inputsR scope.localsR scope.guardR ready.down.2 values locals reads⟩

@[expose] def resolveSite (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    {entry : Ports (Ty V S)} {past : List (Ports (Ty V S))}
    (source : ScopeBoundary imports entry scope.past past)
    {called : MemberSummaries V S} (known : some scope.table = some called)
    (i : Fin called.members.length) (target : Origin entry past (called.at i).fn.port)
    (witnesses : Wires entry past (called.at i).captures) :
    Option (PLift
      ((∀ values locals, source.Reads inputsL scope.localsL values locals →
          (known ▸ scope.guardL : MemberResolution m (some called)) i
            ((Wires.read (.cons target .nil) values locals).get .head) (witnesses.read values locals)) ∧
       (∀ values locals, source.Reads inputsR scope.localsR values locals →
          (known ▸ scope.guardR : MemberResolution m (some called)) i
            ((Wires.read (.cons target .nil) values locals).get .head) (witnesses.read values locals)))) :=
  resolveSiteWith (routeSources checked routes) source known i target witnesses

/-- Check direct calls structurally. At each γ, compose the child boundary
map with the actual argument wires and certify all arms and the suffix.
At a θ, retain only same-port feedback sources while checking the body.
Inline closure descriptions require supplied resolution. -/
@[expose] def synthesizeAtWith (resolve : SourceResolver inputsL inputsR scope) :
    {entry outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    {loops : Bool} → {member : Option (MemberSummaries V S)} →
    (source : ScopeBoundary imports entry scope.past past) → (code : Code Op entry past sigs outs loops member) →
    (known : some scope.table = member) → Option (PLift (resolvedAt source code known inputsL inputsR))
  | _, _, _, _, _, _, _, .ret _, _ => some ⟨fun _ _ _ => trivial, fun _ _ _ => trivial⟩
  | _, _, _, _, _, _, source, .primitive _ _ rest, known => do
    let later ← synthesizeAtWith resolve (source.snoc ⟨fun _ => none⟩) rest known
    pure ⟨fun values locals reads result => later.down.1 values (locals.snoc result)
        (forget_result source inputsL scope.localsL values locals result reads),
      fun values locals reads result => later.down.2 values (locals.snoc result)
        (forget_result source inputsR scope.localsR values locals result reads)⟩
  | _, _, _, _, _, _, source, .callAt i target witnesses _ rest, known => do
    let site ← resolveSiteWith resolve source known i target witnesses
    let later ← synthesizeAtWith resolve (source.snoc ⟨fun _ => none⟩) rest known
    pure ⟨fun values locals reads => ⟨site.down.1 values locals reads,
      fun result => later.down.1 values (locals.snoc result)
        (forget_result source inputsL scope.localsL values locals result reads)⟩,
      fun values locals reads => ⟨site.down.2 values locals reads,
        fun result => later.down.2 values (locals.snoc result)
          (forget_result source inputsR scope.localsR values locals result reads)⟩⟩
  | _, _, _, _, _, _, source, .gamma extra _ _ wires arms rest, known => do
    let entered := source.enter wires
    let joined := entered.join arms
    let children ← collectArms (extra + 2) (fun i =>
      synthesizeAtWith resolve (ScopeBoundary.start entered []) (arms i) known)
    let later ← synthesizeAtWith resolve (source.snoc joined) rest known
    pure ⟨fun values locals reads =>
      let child := wires.read values locals
      let childReads : entered.Reads inputsL scope.localsL child :=
        enter_reads source wires inputsL scope.localsL values locals reads
      ⟨fun i => (children.down i).1 child PUnit.unit (start_reads (past := []) entered inputsL scope.localsL child PUnit.unit childReads),
        fun i result returned => later.down.1 values (locals.snoc result)
          (snoc_reads source joined inputsL scope.localsL values locals result reads
            (join_reads entered arms inputsL scope.localsL child result i childReads returned))⟩,
      fun values locals reads =>
        let child := wires.read values locals
        let childReads : entered.Reads inputsR scope.localsR child :=
        enter_reads source wires inputsR scope.localsR values locals reads
        ⟨fun i => (children.down i).2 child PUnit.unit (start_reads (past := []) entered inputsR scope.localsR child PUnit.unit childReads),
          fun i result returned => later.down.2 values (locals.snoc result)
            (snoc_reads source joined inputsR scope.localsR values locals result reads
              (join_reads entered arms inputsR scope.localsR child result i childReads returned))⟩⟩
  | _, _, _, _, _, _, source, .theta wires body rest, known => do
    let entered := source.enter wires
    let loop := entered.feedback body
    let checkedBody ← synthesizeAtWith resolve (ScopeBoundary.start loop []) body known
    let later ← synthesizeAtWith resolve (source.snoc ⟨fun _ => none⟩) rest known
    pure ⟨fun values locals reads => ⟨fun next stable =>
      let current := wires.read values locals
      let initial : loop.Reads inputsL scope.localsL current :=
        feedback_initial entered body inputsL scope.localsL current
        (enter_reads source wires inputsL scope.localsL values locals reads)
      checkedBody.down.1 next PUnit.unit (start_reads (past := []) loop inputsL scope.localsL next PUnit.unit
        (feedback_preserves entered body inputsL scope.localsL current next initial stable)),
      fun result => later.down.1 values (locals.snoc result)
        (forget_result source inputsL scope.localsL values locals result reads)⟩,
      fun values locals reads => ⟨fun next stable =>
        let current := wires.read values locals
        let initial : loop.Reads inputsR scope.localsR current :=
        feedback_initial entered body inputsR scope.localsR current
          (enter_reads source wires inputsR scope.localsR values locals reads)
        checkedBody.down.2 next PUnit.unit (start_reads (past := []) loop inputsR scope.localsR next PUnit.unit
          (feedback_preserves entered body inputsR scope.localsR current next initial stable)),
        fun result => later.down.2 values (locals.snoc result)
          (forget_result source inputsR scope.localsR values locals result reads)⟩⟩
  | _, _, _, _, _, _, _, _, _ => none
termination_by structural _ _ _ _ _ _ _ code _ => code

@[expose] def synthesizeWith (resolve : SourceResolver inputsL inputsR scope)
    (captures : Wires imports scope.past context) {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)) :
    Option (PLift (resolved captures code inputsL inputsR)) :=
  let source := captureBoundary (params := fn.args) captures
  (synthesizeAtWith resolve (ScopeBoundary.start source past) code rfl).map fun certificate =>
    ⟨fun args locals => certificate.down.1 _ locals
      (start_reads source inputsL scope.localsL _ locals (capture_reads captures inputsL scope.localsL args)),
      fun args locals => certificate.down.2 _ locals
        (start_reads source inputsR scope.localsR _ locals (capture_reads captures inputsR scope.localsR args))⟩

@[expose] def synthesizeAt (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope) :
    {entry outs : Ports (Ty V S)} → {past sigs : List (Ports (Ty V S))} →
    {loops : Bool} → {member : Option (MemberSummaries V S)} →
    (source : ScopeBoundary imports entry scope.past past) → (code : Code Op entry past sigs outs loops member) →
    (known : some scope.table = member) → Option (PLift (resolvedAt source code known inputsL inputsR)) :=
  synthesizeAtWith (routeSources checked routes)

@[expose] def synthesize (checked : scope.Checked actions) (routes : Routes inputsL inputsR scope)
    (captures : Wires imports scope.past context) {past sigs : List (Ports (Ty V S))} {outs : Ports (Ty V S)}
    (code : Code Op (context ++ fn.args) past sigs outs true (some scope.table)) :
    Option (PLift (resolved captures code inputsL inputsR)) :=
  synthesizeWith (routeSources checked routes) captures code

end Check

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Direct
