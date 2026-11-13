module

public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

/-!
# Steps that call no host function

`Step.noHost_of`: a step of code in which no function reference `ref.func a` (at any depth)
names a host function of the store is a step of the host-free semantics `noHost`. Only the
host-call rules (`call_ref-hostfunc-res`/`-div`) use the host, and both fire on a
`ref.func a` naming a host function.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type}

/-- `ref.func a` occurs in the code, at any depth. -/
inductive RefIn (a : Nat) : List Admin → Prop where
  | here {l : List Admin} (h : Admin.ref (.func a) ∈ l) : RefIn a l
  | label {l : List Admin} {n : Nat} {cont : List Instr} {is : List Admin}
      (h : Admin.label n cont is ∈ l) (hi : RefIn a is) : RefIn a l
  | handler {l : List Admin} {n : Nat} {cs : List Catch} {is : List Admin}
      (h : Admin.handler n cs is ∈ l) (hi : RefIn a is) : RefIn a l
  | frame {l : List Admin} {n : Nat} {f : Frame} {is : List Admin}
      (h : Admin.frame n f is ∈ l) (hi : RefIn a is) : RefIn a l

theorem RefIn.mono {a : Nat} {l l' : List Admin} (h : RefIn a l) (hs : ∀ x ∈ l, x ∈ l') :
    RefIn a l' := by
  cases h with
  | here h => exact .here (hs _ h)
  | label h hi => exact .label (hs _ h) hi
  | handler h hi => exact .handler (hs _ h) hi
  | frame h hi => exact .frame (hs _ h) hi

/-- Address `a` holds a host function. -/
def HostAt (s : Store H) (a : Nat) : Prop :=
  ∃ fi hh, s.funcs[a]? = some fi ∧ fi.code = .host hh

/-- No function reference of the code names a host function. -/
def NoHostRef (s : Store H) (code : List Admin) : Prop := ∀ a, RefIn a code → ¬ HostAt s a

theorem NoHostRef.mono {s : Store H} {l l' : List Admin} (h : NoHostRef s l')
    (hs : ∀ x ∈ l, x ∈ l') : NoHostRef s l :=
  fun a ha => h a (ha.mono hs)

theorem NoHostRef.label {s : Store H} {n : Nat} {cont : List Instr} {is : List Admin}
    (h : NoHostRef s [.label n cont is]) : NoHostRef s is :=
  fun a ha => h a (.label List.mem_cons_self ha)

theorem NoHostRef.handler {s : Store H} {n : Nat} {cs : List Catch} {is : List Admin}
    (h : NoHostRef s [.handler n cs is]) : NoHostRef s is :=
  fun a ha => h a (.handler List.mem_cons_self ha)

theorem NoHostRef.frame {s : Store H} {n : Nat} {f : Frame} {is : List Admin}
    (h : NoHostRef s [.frame n f is]) : NoHostRef s is :=
  fun a ha => h a (.frame List.mem_cons_self ha)

theorem NoHostRef.call {s : Store H} {vs : List Val} {a : Nat} {c : Admin}
    (h : NoHostRef s (vals vs ++ [.ref (.func a), c])) {fi : FuncInst H} {hh : H}
    (hf : s.funcs[a]? = some fi) (hc : fi.code = .host hh) : False :=
  h a (.here (by simp)) ⟨fi, hh, hf, hc⟩

/-- A step of code without host references is host-free (curried form). -/
theorem Step.noHost_of' {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : NoHostRef c.store c.code → Step P noHost c c' := by
  induction h with
  | parametric h => exact fun _ => .parametric h
  | numeric h => exact fun _ => .numeric h
  | vector h => exact fun _ => .vector h
  | «variable» h => exact fun _ => .«variable» h
  | table h => exact fun _ => .table h
  | memory h => exact fun _ => .memory h
  | reference h => exact fun _ => .reference h
  | aggregate h => exact fun _ => .aggregate h
  | ctxtInstrs _ hne ih =>
    exact fun hc => .ctxtInstrs (ih (hc.mono fun x hx => by simp [hx])) hne
  | ctxtLabel _ ih => exact fun hc => .ctxtLabel (ih hc.label)
  | ctxtHandler _ ih => exact fun hc => .ctxtHandler (ih hc.handler)
  | ctxtFrame _ ih => exact fun hc => .ctxtFrame (ih hc.frame)
  | block hbt hm => exact fun _ => .block hbt hm
  | loop hbt hm => exact fun _ => .loop hbt hm
  | ifTrue hc => exact fun _ => .ifTrue hc
  | ifFalse => exact fun _ => .ifFalse
  | labelVals => exact fun _ => .labelVals
  | brLabelZero hl hn => exact fun _ => .brLabelZero hl hn
  | brLabelSucc hl => exact fun _ => .brLabelSucc hl
  | brHandler => exact fun _ => .brHandler
  | brIfTrue hc => exact fun _ => .brIfTrue hc
  | brIfFalse => exact fun _ => .brIfFalse
  | brTableLt hi => exact fun _ => .brTableLt hi
  | brTableGe hi => exact fun _ => .brTableGe hi
  | brOnNullNull => exact fun _ => .brOnNullNull
  | brOnNullAddr hv => exact fun _ => .brOnNullAddr hv
  | brOnNonNullNull => exact fun _ => .brOnNonNullNull
  | brOnNonNullAddr hv => exact fun _ => .brOnNonNullAddr hv
  | brOnCastSucceed h => exact fun _ => .brOnCastSucceed h
  | brOnCastFail h => exact fun _ => .brOnCastFail h
  | brOnCastFailSucceed h => exact fun _ => .brOnCastFailSucceed h
  | brOnCastFailFail h => exact fun _ => .brOnCastFailFail h
  | call hx hf => exact fun _ => .call hx hf
  | callRefNull hc => exact fun _ => .callRefNull hc
  | callRefFunc hc hf he hn hcode => exact fun _ => .callRefFunc hc hf he hn hcode
  | callRefHost _ hf _ _ hcode => exact fun hc => (hc.call hf hcode).elim
  | callRefHostDiv _ hf _ _ hcode => exact fun hc => (hc.call hf hcode).elim
  | returnCall hx hf => exact fun _ => .returnCall hx hf
  | returnCallRefLabel hc => exact fun _ => .returnCallRefLabel hc
  | returnCallRefHandler hc => exact fun _ => .returnCallRefHandler hc
  | returnCallRefFrameNull hc => exact fun _ => .returnCallRefFrameNull hc
  | returnCallRefFrameAddr hc hf he hn => exact fun _ => .returnCallRefFrameAddr hc hf he hn
  | callIndirect => exact fun _ => .callIndirect
  | returnCallIndirect => exact fun _ => .returnCallIndirect
  | frameVals hn => exact fun _ => .frameVals hn
  | returnFrame hn => exact fun _ => .returnFrame hn
  | returnLabel => exact fun _ => .returnLabel
  | returnHandler => exact fun _ => .returnHandler
  | throw ht he hn => exact fun _ => .throw ht he hn
  | throwRefNull => exact fun _ => .throwRefNull
  | throwRefInstrs hne => exact fun _ => .throwRefInstrs hne
  | throwRefLabel => exact fun _ => .throwRefLabel
  | throwRefFrame => exact fun _ => .throwRefFrame
  | throwRefHandlerEmpty => exact fun _ => .throwRefHandlerEmpty
  | throwRefHandlerCatch he ht => exact fun _ => .throwRefHandlerCatch he ht
  | throwRefHandlerCatchRef he ht => exact fun _ => .throwRefHandlerCatchRef he ht
  | throwRefHandlerCatchAll => exact fun _ => .throwRefHandlerCatchAll
  | throwRefHandlerCatchAllRef => exact fun _ => .throwRefHandlerCatchAllRef
  | throwRefHandlerNext h => exact fun _ => .throwRefHandlerNext h
  | tryTable hbt hm => exact fun _ => .tryTable hbt hm
  | handlerVals => exact fun _ => .handlerVals
  | trapInstrs hne => exact fun _ => .trapInstrs hne
  | trapLabel => exact fun _ => .trapLabel
  | trapHandler => exact fun _ => .trapHandler
  | trapFrame => exact fun _ => .trapFrame

/-- **A step of code without host references is host-free.** -/
theorem Step.noHost_of {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (hc : NoHostRef c.store c.code) : Step P noHost c c' :=
  Step.noHost_of' h hc

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
