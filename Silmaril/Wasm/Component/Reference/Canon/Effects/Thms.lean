module

public import Silmaril.Wasm.Component.Reference.Canon.Effects.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Defs
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Defs
public import Silmaril.Wasm.Component.Reference.Value.Nan.Defs
public import Silmaril.Wasm.Component.Reference.Value.Typing.Defs
public import Silmaril.Wasm.Component.Reference.Trap.Defs
public import Silmaril.Wasm.Component.Reference.Instantiate.Items.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Options.Thms

/-!
# `Canon.Effects`: laws of the component reference

Theorems of the component reference copy `Canon.Effects`, refined out of
`Silmaril.Raw.Wasm.Component.Canon.Effects`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Runtime.InstState

theorem addHandle_eq {e : HandleEntry} {st st' : InstState} {i : Nat}
    (h : addHandle? e st = some (i, st')) : addHandle e st = st' := by
  simp [addHandle, h]

theorem removeHandle_eq {i : Nat} {st st' : InstState} {e : HandleEntry}
    (h : removeHandle? i st = some (e, st')) : removeHandle i st = st' := by
  simp [removeHandle, h]

end Silmaril.Wasm.Component.Runtime.InstState

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type} {α β : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem bind {p : P E σ α} {f : α → P E σ β} (hp : P.Inv I p) (hf : ∀ a, P.Inv I (f a)) :
    P.Inv I (p >>= f) := Prog.Every.bind hp hf

theorem map {p : P E σ α} {f : α → β} (hp : P.Inv I p) : P.Inv I (f <$> p) := by
  rw [map_eq_pure_bind]
  exact bind hp fun _ => pure _

theorem ite {c : Prop} [Decidable c] {p q : P E σ α} (hp : P.Inv I p) (hq : P.Inv I q) :
    P.Inv I (if c then p else q) := by
  split
  · exact hp
  · exact hq

theorem mapM {f : α → P E σ β} {xs : List α} (h : ∀ a ∈ xs, P.Inv I (f a)) :
    P.Inv I (Prog.mapM f xs) := Prog.Every.mapM h

theorem forM {f : α → P E σ PUnit} {xs : List α} (h : ∀ a ∈ xs, P.Inv I (f a)) :
    P.Inv I (Prog.forM xs f) := Prog.Every.forM h

theorem foldlM {f : β → α → P E σ β} {b : β} {xs : List α}
    (h : ∀ b, ∀ a ∈ xs, P.Inv I (f b a)) : P.Inv I (Prog.foldlM f b xs) :=
  Prog.Every.foldlM h

theorem listFoldlM {f : β → α → P E σ β} {b : β} {xs : List α}
    (h : ∀ b, ∀ a ∈ xs, P.Inv I (f b a)) : P.Inv I (List.foldlM f b xs) := by
  rw [← Prog.foldlM_eq_list_foldlM]; exact foldlM h

/-- A single non-`modify` operation. -/
theorem perform {o : Op E σ} (h : Op.PreservesInv I o) : P.Inv I (Canon.perform o) :=
  Prog.Every.lift h

theorem trap (r : TrapReason) : P.Inv I (Canon.trap r : P E σ α) :=
  Prog.Every.op trivial (fun e => nomatch e)

theorem internal (msg : String) : P.Inv I (Canon.internal msg : P E σ α) := trap _

theorem trapIf (c : Bool) (r : TrapReason) : P.Inv I (Canon.trapIf c r : P E σ Unit) := by
  unfold Canon.trapIf; split
  · exact trap r
  · exact pure ()

theorem orTrap (r : TrapReason) (o : Option α) : P.Inv I (Canon.orTrap r o : P E σ α) := by
  cases o
  · exact trap r
  · exact pure _

theorem getStore : P.Inv I (Canon.getStore : P E σ (CStore E)) := perform trivial

theorem gets (f : CStore E → α) : P.Inv I (Canon.gets f : P E σ α) :=
  bind getStore fun _ => pure _

theorem modifyStore {f : CStore E → CStore E} (h : ∀ s, I s → I (f s)) :
    P.Inv I (Canon.modifyStore f : P E σ Unit) := perform h

theorem choose (k : ChoiceKind) : P.Inv I (Canon.choose k : P E σ k.Resp) := perform trivial

theorem callCore (f : E.FuncAddr) (args : List FlatValue) :
    P.Inv I (Canon.callCore f args : P E σ _) := perform trivial

theorem callRet (c : Call E) : P.Inv I (Canon.callRet c : P E σ (Ret E)) := perform trivial

theorem currentThread : P.Inv I (Canon.currentThread : P E σ _) := perform trivial

theorem newThread (b : ThreadBody E) : P.Inv I (Canon.newThread b : P E σ _) :=
  perform trivial

theorem block (sw : Option ThreadId) : P.Inv I (Canon.block sw : P E σ _) := perform trivial

theorem resumeThread (t : ThreadId) : P.Inv I (Canon.resumeThread t : P E σ _) :=
  perform trivial

theorem hostGet : P.Inv I (Canon.hostGet : P E σ σ) := perform trivial

theorem emit (o : HostObs) : P.Inv I (Canon.emit o : P E σ Unit) := perform trivial

theorem pickTick (c : α) (cs : List α) : P.Inv I (Canon.pickTick c cs : P E σ α) :=
  bind (choose _) fun _ => pure _

theorem pickSyncLoop (c : α) (cs : List α) : P.Inv I (Canon.pickSyncLoop c cs : P E σ α) :=
  bind (choose _) fun _ => pure _

theorem shuffle (xs : List α) : P.Inv I (Canon.shuffle xs : P E σ (List α)) :=
  bind (choose _) fun _ => pure _

private theorem callDecode {γ : Type} (c : Call E) (g : Ret E → P E σ γ)
    (hg : ∀ r, P.Inv I (g r)) : P.Inv I (Canon.callRet c >>= g) := bind (callRet c) hg

theorem callUnit (c : Call E) : P.Inv I (Canon.callUnit c : P E σ Unit) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callNat (c : Call E) : P.Inv I (Canon.callNat c : P E σ Nat) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callVals (c : Call E) : P.Inv I (Canon.callVals c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callCancel (c : Call E) : P.Inv I (Canon.callCancel c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem callItems (c : Call E) : P.Inv I (Canon.callItems c : P E σ _) :=
  callDecode c _ fun r => by cases r <;> first | exact pure _ | exact internal _

theorem allocObj {Id : Type} (F : ArenaField E Id α) (x : α)
    (h : ∀ s, I s → I (ArenaOps.allocSt F x s)) : P.Inv I (Canon.allocObj F x : P E σ Id) :=
  bind getStore fun _ => bind (modifyStore h) fun _ => pure _

theorem getObj {Id : Type} (F : ArenaField E Id α) (i : Id) :
    P.Inv I (Canon.getObj F i : P E σ α) :=
  bind getStore fun s => by
    cases F.get? s i <;> first | exact pure _ | exact internal _

theorem modifyObj {Id : Type} (F : ArenaField E Id α) (i : Id) (f : α → α)
    (h : ∀ s, I s → I (ArenaOps.updateSt F i f s)) :
    P.Inv I (Canon.modifyObj F i f : P E σ Unit) := modifyStore h

theorem getThread (t : ThreadId) : P.Inv I (Canon.getThread t : P E σ Thread) := getObj _ _

theorem getTask (t : TaskId) : P.Inv I (Canon.getTask t : P E σ (Task E)) := getObj _ _

theorem getInst (i : InstId) : P.Inv I (Canon.getInst i : P E σ InstState) := getObj _ _

theorem currentTask? : P.Inv I (Canon.currentTask? : P E σ _) :=
  bind currentThread fun t => by
    cases t
    · exact pure _
    · exact bind (getThread _) fun _ => pure _

theorem currentInst? : P.Inv I (Canon.currentInst? : P E σ _) :=
  bind currentTask? fun t => by
    cases t
    · exact pure _
    · exact bind (getTask _) fun _ => pure _

theorem currentThreadId : P.Inv I (Canon.currentThreadId : P E σ _) :=
  bind currentThread fun t => by cases t <;> first | exact pure _ | exact internal _

theorem currentTask : P.Inv I (Canon.currentTask : P E σ _) :=
  bind currentTask? fun t => by cases t <;> first | exact pure _ | exact internal _

theorem currentInst : P.Inv I (Canon.currentInst : P E σ _) :=
  bind currentInst? fun t => by cases t <;> first | exact pure _ | exact internal _

theorem modifyInst (inst : InstId) {f : InstState → InstState}
    (h : ∀ s, I s → I (ArenaField.insts.modify s inst f)) :
    P.Inv I (Canon.modifyInst inst f : P E σ Unit) := modifyObj _ _ _ h

theorem handlesAdd (inst : InstId) (e : HandleEntry)
    (h : ∀ s, I s → I (ArenaField.insts.modify s inst (InstState.addHandle e))) :
    P.Inv I (Canon.handlesAdd inst e : P E σ Nat) :=
  bind (getInst inst) fun st => by
    cases st.addHandle? e with
    | none => exact trap _
    | some r => exact bind (modifyInst inst h) fun _ => pure _

theorem handlesGet (inst : InstId) (i : Nat) :
    P.Inv I (Canon.handlesGet inst i : P E σ HandleEntry) :=
  bind (getInst inst) fun _ => orTrap _ _

theorem handlesRemove (inst : InstId) (i : Nat)
    (h : ∀ s, I s → I (ArenaField.insts.modify s inst (InstState.removeHandle i))) :
    P.Inv I (Canon.handlesRemove inst i : P E σ HandleEntry) :=
  bind (getInst inst) fun st => by
    cases st.removeHandle? i with
    | none => exact trap _
    | some r => exact bind (modifyInst inst h) fun _ => pure _

theorem threadsGet (inst : InstId) (i : Nat) :
    P.Inv I (Canon.threadsGet inst i : P E σ ThreadId) :=
  bind (getInst inst) fun _ => orTrap _ _

end P.Inv

end Silmaril.Wasm.Component.Canon

namespace Silmaril.Wasm.Component.Canon

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value
variable {E : CoreEngine} {σ : Type} {α β : Type}

namespace P.Inv

variable {I : CStore E → Prop}

theorem hostSet (s : σ) : P.Inv I (Canon.hostSet s : P E σ Unit) := perform trivial

end P.Inv

end Silmaril.Wasm.Component.Canon
