module

public import Silmaril.Wasm.Det.Stateless.Defs
public import Silmaril.Proofs.Wasm.Det.Stateless.Check
public import Silmaril.Proofs.Wasm.Det.Stateless.VC

/-!
# Stateless code modulo traps and imports: theorems

Every statement holds at an **arbitrary** profile `P` (silmaril-lean's Core 3.0 `Step P`),
against arbitrary import answers (`Silmaril.Wasm.Det.Core.Runs`).

**The subset is deterministic and stateless.** Steps of subset code (`Inv A R W`) are steps of
every profile (`step_profile`) and change the store at most by a `global.set` to a global of `W`.
Hence:

* `detCfg_of_inv`, `detFn_of_good`: subset code is deterministic modulo traps and imports
  (`Silmaril.Wasm.Det.Core.DetCfg`/`DetFn`);
* `obsAgree_of_agree`, `statelessFn_of_good`: from two stores that agree on the functions and on
  the globals the code reads (`Agree R`), the same frame and code have the same non-trapping
  outputs against the same answers: a subset function is **stateless** over these stores
  (`Silmaril.Wasm.Det.Core.StatelessFn`). With `R` empty (no globals: the obvious subset) the
  stores need only hold the same functions.

**Modules.**

* `callReach_outside`: if every entry function of a module is in the subset with write set `W`,
  every call state differs from the initial store only at the globals of `W`;
* `statelessFn_callReach`: a subset function reading no global of `W` is stateless over the call
  states of such a module, although the module itself need not be stateless;
* `statelessFn_callReach_funcs`: a subset function reading no global is stateless over the call
  states of **every** module (the other functions are arbitrary Wasm 3.0 code);
* `statelessModule_of_good`, `detModule_of_good`: a module whose entries are subset functions
  without global writes is stateless; with global writes, deterministic.

**Checkers and the tactic.** `checkSet_sound` (only the final check is trusted), then
`statelessFn_of_check`, `statelessFn_callReach_of_check`, `statelessModule_of_check`,
`detFn_of_check`, `detFn_callReach_of_check`, `detModule_of_check`. The tactic
**`wasm_stateless`** closes, for a concrete store, `StatelessFn P (CallReach P Entry s₀) a`,
`StatelessModule P Entry s₀`, `DetFn P s a`, `CallReach P Entry s₀ s → DetFn P s a` and
`DetModule P Entry s₀` by kernel evaluation of the corresponding check.

**VCs (the every-run Hoare logic).** For functions that touch state but whose results do not
depend on it (a scratch global written before it is read, state restored, reads of state the
call states agree on), statelessness follows from a unary specification:
`statelessFn_of_hwp` (every run from every call state returns `F vs` or traps, as an
`HWP P Det.noHost` of the invocation) and `statelessFn_of_fspec` (a valid function
specification of `Silmaril.Wasm.Logic.Hoare` whose postcondition fixes the results). The rules
`hwp_globalGet`, `hwp_globalSet` extend the logic to globals.

Proofs: `Silmaril.Proofs.Wasm.Det.Stateless.{Basic,Step,Runs,Check,VC}`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare (HWP FSpec FSpecValid)

variable {A R W : Nat → Bool}

/-! ## Subset code -/

/-- **A step of subset code is a step of every profile.** -/
theorem step_profile {P P' : Profile} {c c' : Config Nat} (hc : Inv A R W c)
    (h : Step P Det.noHost c c') : Step P' Det.noHost c c' :=
  Silmaril.Proofs.Wasm.Det.Stateless.step_profile hc h

/-- The invariant holds of the invocation of a function of `A`. -/
theorem inv_invoke {s : Store Nat} {a : Nat} (vs : List Val) (hg : GoodFuns A R W s.funcs)
    (ha : A a = true) : Inv A R W (invoke s a vs) :=
  Silmaril.Proofs.Wasm.Det.Stateless.inv_invoke vs hg ha

/-- **Subset code is deterministic modulo traps and imports**, at every profile. -/
theorem detCfg_of_inv {P : Profile} {c : Config Nat} (hc : Inv A R W c) : DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.Stateless.detCfg_of_inv hc

/-- **Subset code does not depend on the state it does not read**: from the same frame and code
in two stores agreeing on the functions and the globals of `R`, the same answers give the same
non-trapping outputs, at every profile. -/
theorem obsAgree_of_agree {P : Profile} {c₁ c₂ : Config Nat} (hc : Inv A R W c₁)
    (hag : Agree R c₁.store c₂.store) (hf : c₁.frame = c₂.frame) (hcode : c₁.code = c₂.code) :
    ObsAgree P c₁ c₂ :=
  Silmaril.Proofs.Wasm.Det.Stateless.obsAgree_of_agree hc hag hf hcode

/-! ## Functions -/

/-- **Per function: subset functions are deterministic**, at every profile. -/
theorem detFn_of_good {P : Profile} {s : Store Nat} {a : Nat} (hg : GoodFuns A R W s.funcs)
    (ha : A a = true) : DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.Stateless.detFn_of_good hg ha

/-- **Per function: subset functions are stateless** over the stores agreeing with `s₀` on the
functions and the globals they read, at every profile. -/
theorem statelessFn_of_good {P : Profile} {s₀ : Store Nat} {a : Nat}
    (hg : GoodFuns A R W s₀.funcs) (ha : A a = true) :
    StatelessFn P (fun s => Agree R s s₀) a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_of_good hg ha

/-! ## Modules -/

/-- **Frame property**: the call states of a module whose entries are subset functions with write
set `W` agree with the initial store outside `W`. -/
theorem callReach_outside {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hg : GoodFuns A R W s₀.funcs) (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true)
    (hs : CallReach P Entry s₀ s) : Outside W s s₀ :=
  Silmaril.Proofs.Wasm.Det.Stateless.callReach_outside hg hE hs

/-- The call states of such a module have the globals of the initial store. -/
theorem callReach_length {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat}
    (hg : GoodFuns A R W s₀.funcs) (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true)
    (hs : CallReach P Entry s₀ s) : s.globals.length = s₀.globals.length :=
  Silmaril.Proofs.Wasm.Det.Stateless.callReach_length hg hE hs

/-- **A subset function is stateless over the call states of a module** whose entries are subset
functions (`hm`, writing the globals of `W`), when it reads no global of `W`. -/
theorem statelessFn_callReach {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat} {a : Nat}
    {Am Rm : Nat → Bool} (hm : GoodFuns Am Rm W s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → Am a = true)
    {W' : Nat → Bool} (hf : GoodFuns A R W' s₀.funcs) (ha : A a = true)
    (hRW : ∀ g, R g = true → W g = false) : StatelessFn P (CallReach P Entry s₀) a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_callReach hm hE hf ha hRW

/-- **A subset function reading no global is stateless over the call states of every module**,
whatever the module's other functions do. -/
theorem statelessFn_callReach_funcs {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat} {a : Nat}
    (hf : GoodFuns A (fun _ => false) W s₀.funcs) (ha : A a = true) :
    StatelessFn P (CallReach P Entry s₀) a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_callReach_funcs hf ha

/-- **Per module: entries in the subset without global writes give a stateless module.** -/
theorem statelessModule_of_good {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A R (fun _ => false) s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true) :
    StatelessModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessModule_of_good hm hE

/-- **Per module: entries in the subset give a deterministic module.** -/
theorem detModule_of_good {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (hm : GoodFuns A R W s₀.funcs)
    (hE : ∀ a fi, Entry a → s₀.funcs[a]? = some fi → A a = true) : DetModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.Stateless.detModule_of_good hm hE

/-! ## Checkers -/

/-- `checkSet` decides `GoodFuns` on a concrete store. -/
theorem checkSet_sound {H : Type} {s : Store H} {A : List Nat} {R W : Nat → Bool}
    (h : checkSet s A R W = true) : GoodFuns A.contains R W s.funcs :=
  Silmaril.Proofs.Wasm.Det.Stateless.checkSet_sound h

theorem statelessFn_of_check {P : Profile} {s : Store Nat} {a : Nat}
    (h : statelessCheck s a = true) :
    StatelessFn P (fun t => Agree (readsOf s (closure s [a])).contains t s) a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_of_check h

theorem statelessFn_callReach_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    {a : Nat} (h : crCheck s₀ a = true) : StatelessFn P (CallReach P Entry s₀) a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_callReach_of_check h

theorem statelessModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : moduleStatelessCheck s₀ = true) : StatelessModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessModule_of_check h

theorem detFn_of_check {P : Profile} {s : Store Nat} {a : Nat} (h : detCheck s a = true) :
    DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.Stateless.detFn_of_check h

theorem detFn_callReach_of_check {P : Profile} {Entry : Nat → Prop} {s₀ s : Store Nat} {a : Nat}
    (h : detCheck s₀ a = true) (hs : CallReach P Entry s₀ s) : DetFn P s a :=
  Silmaril.Proofs.Wasm.Det.Stateless.detFn_callReach_of_check h hs

theorem detModule_of_check {P : Profile} {Entry : Nat → Prop} {s₀ : Store Nat}
    (h : moduleCheck s₀ = true) : DetModule P Entry s₀ :=
  Silmaril.Proofs.Wasm.Det.Stateless.detModule_of_check h

/-- Closes `StatelessFn P (CallReach P Entry s₀) a`, `StatelessModule P Entry s₀`,
`DetFn P s a`, `CallReach P Entry s₀ s → DetFn P s a` or `DetModule P Entry s₀` for a concrete
store, by kernel evaluation of the corresponding check (`crCheck`, `moduleStatelessCheck`,
`detCheck`, `moduleCheck`). -/
macro "wasm_stateless" : tactic => `(tactic| first
  | exact Silmaril.Wasm.Det.Stateless.statelessFn_callReach_of_check (by decide +kernel)
  | exact Silmaril.Wasm.Det.Stateless.statelessModule_of_check (by decide +kernel)
  | exact Silmaril.Wasm.Det.Stateless.detFn_of_check (by decide +kernel)
  | exact fun _ hs => Silmaril.Wasm.Det.Stateless.detFn_callReach_of_check (by decide +kernel) hs
  | exact Silmaril.Wasm.Det.Stateless.detModule_of_check (by decide +kernel))

/-! ## VCs -/

/-- **Statelessness from an every-run specification** (`HWP`, closed world): every run from every
call state returns `F vs` or traps. -/
theorem statelessFn_of_hwp {P : Profile} {S : Store Nat → Prop} {a : Nat}
    (F : List Val → List Val)
    (h : ∀ s vs, S s → InvokeOk s a vs →
      HWP P Det.noHost s {} (invoke s a vs).code (fun _ _ o => o = .normal (F vs) ∨ o = .trap)) :
    StatelessFn P S a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_of_hwp F h

/-- **Statelessness from a valid function specification** fixing the results. -/
theorem statelessFn_of_fspec {P : Profile} {S : Store Nat → Prop} {a : Nat} {Sp : FSpec Nat}
    (F : List Val → List Val) (hv : FSpecValid P Det.noHost a Sp)
    (hpre : ∀ s vs, S s → InvokeOk s a vs → Sp.pre s vs)
    (hpost : ∀ s vs s' o, Sp.post s vs s' o → o = .normal (F vs) ∨ o = .trap) :
    StatelessFn P S a :=
  Silmaril.Proofs.Wasm.Det.Stateless.statelessFn_of_fspec F hv hpre hpost

/-- **The `global.get` rule** of the every-run logic. -/
theorem hwp_globalGet {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {vs : List Val} {x : GlobalIdx} {a : Nat} {g : GlobalInst} {rest : List Admin} {Q : Post H}
    (hg : s.global? f x = some (a, g)) (h : HWP P host s f (vals (vs ++ [g.value]) ++ rest) Q) :
    HWP P host s f (vals vs ++ .plain (.globalGet x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Det.Stateless.hwp_globalGet hg h

/-- **The `global.set` rule** of the every-run logic. -/
theorem hwp_globalSet {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {vs : List Val} {x : GlobalIdx} {a : Nat} {g : GlobalInst} {v : Val} {rest : List Admin}
    {Q : Post H} (hg : s.global? f x = some (a, g))
    (h : HWP P host (s.setGlobal a v) f (vals vs ++ rest) Q) :
    HWP P host s f (vals (vs ++ [v]) ++ .plain (.globalSet x) :: rest) Q :=
  Silmaril.Proofs.Wasm.Det.Stateless.hwp_globalSet hg h

end Silmaril.Wasm.Det.Stateless
