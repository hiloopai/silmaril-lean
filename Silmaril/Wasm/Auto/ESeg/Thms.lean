module

public import Silmaril.Wasm.Auto.ESeg.Defs
public import Silmaril.Wasm.Auto.EGraph.Thms
public import Silmaril.Wasm.Auto.XExec.Thms
public import Silmaril.Wasm.Auto.Equiv.Thms
public import Silmaril.Wasm.Auto.Rules.Thms
public import Silmaril.Wasm.Examples.Common.Thms
import Silmaril.Proofs.Wasm.Auto.ESeg.LogicS

/-!
# E-graph certificates for segments with locals: soundness

## Segments and bodies

Proofs in `Silmaril.Proofs.Wasm.Auto.ESeg.{Comp2,XCheck,Check}` and, for the
instruction-by-instruction lifting lemma, `Silmaril.Raw.Wasm.Auto.ESeg.Lift`.

* `comp2?_eval`: the second family of computed rewrites (`shiftShift?`, `cmpZero?`,
  `signTest?`, `sremEqz?`, `sdivPow2?`: shifts of shifts, unsigned comparisons with `0` and
  `1`, `x <s 0` as `x >>u 31`, `eqz (x %s 2^k)` as `eqz (x & (2^k - 1))`, and signed division
  by `2^k` in the bias form `(x + ((x >>s (w-1)) >>u (w-k))) >>s k`) keeps the value of a term
  for every operand;
* `checkEqX_sound`: an extended chain keeps the value in every frame typed by `Γ`;
* `coversOk_sound`: covers transfer "no term traps" from one side to the other;
* `lift_exec`: the run of a lifted segment (`nop`, `drop`, constants, `local.get`/`set`/`tee`,
  integer operators) is what its effect summary denotes, traps included;
* **`segEquiv_of_checkSeg`**: a checked certificate gives `Silmaril.Wasm.Auto.EGraph.SegEquiv Γ a b`
  for the instruction lists `a` and `b` themselves (same store, frame, stack and failures);
* **`bodyEquiv_of_checkBody`**: a checked certificate gives `BodyEquiv Γ a b` (the same up to
  the locals, which are dead after a function body).

The link to the every-run logic is below.

## `select` and function entry

Proofs in `Silmaril.Proofs.Wasm.Auto.ESeg.Select` and, for the lifting lemmas,
`Silmaril.Proofs.Wasm.Auto.ESeg.LiftS`.

* `selTerm_eval`: on `i32` values, `selTerm a b c = b ^ ((a ^ b) & (0 - (c ≠ 0)))` is `select`;
* `liftSel_exec`: in a frame typed by `Γ`, `Silmaril.Wasm.Auto.XExec.execS` (`exec` with `select`) of
  a lifted segment is what its summary denotes, traps included;
* `den_entry`, `liftEntrySel_exec`: lifting from function entry (parameters, then zero declared
  locals) is sound in every entry frame;
* **`segEquivSel_of_checkSegSel`**, **`bodyEquivSel_of_checkBodySel`**: the segment and body
  checkers
  with `select`;
* **`funcEquiv_of_checkFunc`**: `FuncEquiv Γ da db a b` for bodies with the same parameters `Γ`
  and different declared locals `da`, `db` (renumbered, merged or retyped locals): from
  function entry with the same arguments, in frames of the same module, they fail together or
  end with the same store and stack. The terms of both summaries read parameters only
  (`readsBelow`, checked), so they have the same value in both frames (`eval_agree`).

The every-run reading, traps included, is below.

## The every-run logic

Proofs in `Silmaril.Proofs.Wasm.Auto.ESeg.Logic`. For segments whose effect summary is
typed and trap-free (`Silmaril.Wasm.Auto.ESeg.checkPure`, decided by `decide`):

* **`equivSeg_of_segEquiv`**: the exec-level `Silmaril.Wasm.Auto.EGraph.SegEquiv Γ a b` (what the
  certificate checkers prove) gives the equiv track's every-run
  `Silmaril.Wasm.Auto.Equiv.SegEquiv Γ [] a b` (the weakest preconditions `Wp m P host` agree in
  every context, both readings, every profile and host relation);
* **`outEquiv_of_bodyEquiv`**: `Silmaril.Wasm.Auto.ESeg.BodyEquiv Γ a b` gives
  `Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b`: the same for function bodies and every
  postcondition blind to the locals (`funcPost`, `bodyPost`), the function-level statement;
* `pure_runs`, `wp_exec_iff`, `wp_vals_iff`, `frameOk_frameAt`: the pieces.

Example: `tee_form_everyRun` below.

## `select`, traps and renumbered locals in the every-run logic

Proofs in `Silmaril.Proofs.Wasm.Auto.ESeg.LogicS`. Typedness (`ESeg.typedBody`: the
validator `XExec.tsteps` accepts the body) and the absence of division (`ESeg.noDiv`) are
decided by `decide`.

* **`outEquivSel_of_bodyEquivSel`**: `ESeg.BodyEquivSel Γ a b` gives
  `Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b` for typed bodies, **trapping or not**: typed code
  is never stuck (`XExec.xexec_typed`), so when one body fails both trap, in the same store and
  module, and the every-run weakest precondition of each is the trap postcondition at its trap
  (`XExec.wp_xexec_trap_iff`), which a postcondition blind to the locals cannot tell apart;
* `outEquiv_of_bodyEquiv_typed`: the same for the `select`-free `ESeg.BodyEquiv` of the pass-2
  certificates (their trapping bodies had no every-run reading before);
* **`equivSeg_of_segEquivSel`**: `ESeg.SegEquivSel Γ a b` gives `Equiv.SegEquiv Γ [] a b` for
  typed segments without division (segments with `select`);
* **`funcOutEquiv_of_funcEquiv`**: `ESeg.FuncEquiv Γ da db a b` gives `FuncOutEquiv Γ da db a b`
  (bodies with different declared locals, every run, traps included);
* `wp_iff_of_outEq`, `wp_typed`: the pieces.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.ESeg

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.ESeg` -/

section
-- from Silmaril/Proofs/Wasm/Auto/ESeg/Comp2.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

theorem ltu_one (t : IntType) (x : BitVec t.width) :
    intRelOp t (.lt .unsigned) x (BitVec.ofNat _ 1) = intTestOp t .eqz x :=
  Silmaril.Proofs.Wasm.Auto.ESeg.ltu_one (t := t) (x := x)

theorem gtu_zero (t : IntType) (x : BitVec t.width) :
    intRelOp t (.gt .unsigned) x (BitVec.ofNat _ 0) = intRelOp t .ne x (BitVec.ofNat _ 0) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.gtu_zero (t := t) (x := x)

end

section
-- from Silmaril/Raw/Wasm/Auto/ESeg/Comp2.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

/-- The bias form of signed division by `2^k`, through `toNat`. -/
theorem sdiv_pow2 {w k : Nat} (hk0 : 0 < k) (hk : k < w - 1) (x : BitVec w) :
    x.sdiv (BitVec.ofNat w (2 ^ k)) =
      (x + ((x.sshiftRight (w - 1)) >>> (w - k))).sshiftRight k :=
  Silmaril.Proofs.Wasm.Auto.ESeg.sdiv_pow2 (w := w) (k := k) (hk0 := hk0) (hk := hk) (x := x)

/-- **The second family of computed rewrites keeps the value.** -/
theorem comp2?_eval {f : Frame} {a b : Term} (h : comp2? a = some b) : a.eval f = b.eval f :=
  Silmaril.Proofs.Wasm.Auto.ESeg.comp2?_eval (f := f) (a := a) (b := b) (h := h)

theorem const_val {f : Frame} {t t' : IntType} {n : Nat} {y : BitVec t.width}
    (h : (Term.const t' n).eval f = some (intVal t y)) (htt : t' = t) :
    y = BitVec.ofNat t.width n :=
  Silmaril.Proofs.Wasm.Auto.ESeg.const_val (f := f) (t := t) (t' := t') (n := n) (y := y) (h := h)
    (htt := htt)

/-- A binary operator that `safeBinOp` admits does not trap. -/
theorem intBinOp_ok_of_safe {f : Frame} {t : IntType} {op : IntBinOp} {b : Term}
    {x y : BitVec t.width}
    (hs : safeBinOp t op b = true) (hb : b.eval f = some (intVal t y)) :
    ∃ z, intBinOp t op x y = .ok z :=
  Silmaril.Proofs.Wasm.Auto.ESeg.intBinOp_ok_of_safe (f := f) (t := t) (op := op) (b := b) (x := x)
    (y := y) (hs := hs) (hb := hb)

end

section
-- from Silmaril/Proofs/Wasm/Auto/ESeg/XCheck.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

/-- **An extended chain keeps the value.** -/
theorem runX_sound {Γ : List IntType} {rules : List Rule} {f : Frame} (hR : ∀ r ∈ rules, r.Sound)
    (hf : FrameOk Γ f) :
    ∀ {ss : List XStep} {e e' : Term}, runX Γ rules e ss = some e' → e.eval f = e'.eval f :=
  Silmaril.Proofs.Wasm.Auto.ESeg.runX_sound (Γ := Γ) (rules := rules) (f := f) (hR := hR) (hf := hf)

/-- **Soundness of the extended equivalence checker.** -/
theorem checkEqX_sound {Γ : List IntType} {rules : List Rule} {f : Frame}
    (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {e₁ e₂ : Term}
    {ss : List XStep} (h : checkEqX Γ rules e₁ e₂ ss = true) : e₁.eval f = e₂.eval f :=
  Silmaril.Proofs.Wasm.Auto.ESeg.checkEqX_sound (Γ := Γ) (rules := rules) (f := f) (hR := hR)
    (hf := hf) (e₁ := e₁) (e₂ := e₂) (ss := ss) (h := h)

/-- **Covers are sound**: if every term of the other side has a value, so has every term of
this side. -/
theorem coversOk_sound {Γ : List IntType} {rules : List Rule} {f : Frame}
    (hR : ∀ r ∈ rules, r.Sound) (hf : FrameOk Γ f) {other : List Term}
    (ho : ∀ r ∈ other, (r.eval f).isSome) :
    ∀ {es : List Term} {cs : List Cover}, coversOk Γ rules other es cs = true →
      ∀ e ∈ es, (e.eval f).isSome :=
  Silmaril.Proofs.Wasm.Auto.ESeg.coversOk_sound (Γ := Γ) (rules := rules) (f := f) (hR := hR)
    (hf := hf) (other := other) (ho := ho)

end

section
-- from Silmaril/Raw/Wasm/Auto/ESeg/Lift.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph

theorem den_of {f : Frame} {S : Sym} {gs ls vs : List Val} (hg : evalL f S.guards = some gs)
    (hl : evalL f S.locs = some ls) (hv : evalL f S.stack = some vs) :
    den f S = some (setLocs f ls, vs) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.den_of (f := f) (S := S) (gs := gs) (ls := ls) (vs := vs) (hg := hg)
    (hl := hl) (hv := hv)

/-- **Lifting is sound**: the run of a lifted segment is what its summary denotes. -/
theorem lift_exec {f : Frame} {Γ : List IntType} {a : List Instr} {A : Sym} (hl : Γ.length < 2 ^ 32)
    (h : lift Γ.length a = some A) {H : Type} (s : Store H) (rs : List Val) (hf : FrameOk Γ f) :
    exec s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.lift_exec (f := f) (Γ := Γ) (a := a) (A := A) (hl := hl) (h := h)
    (H := H) (s := s) (rs := rs) (hf := hf)

end

section
-- from Silmaril/Proofs/Wasm/Auto/ESeg/Check.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph

/-- **Soundness of the segment checker.** -/
theorem segEquiv_of_checkSeg {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkSeg Γ rules a b c = true) :
    SegEquiv Γ a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.segEquiv_of_checkSeg (Γ := Γ) (rules := rules) (a := a) (b := b)
    (c := c) (hR := hR) (h := h)

/-- **Soundness of the body checker.** -/
theorem bodyEquiv_of_checkBody {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkBody Γ rules a b c = true) :
    BodyEquiv Γ a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.bodyEquiv_of_checkBody (Γ := Γ) (rules := rules) (a := a) (b := b)
    (c := c) (hR := hR) (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/ESeg/Select.lean

open Silmaril.Wasm Silmaril.Wasm.Auto
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec

/-- A term that reads only parameters has the same value in frames with the same
parameters. -/
theorem eval_agree {n : Nat} {fa fb : Frame} (hp : SameParams n fa fb) :
    ∀ {e : Term}, readsBelow n e = true → e.eval fa = e.eval fb :=
  Silmaril.Proofs.Wasm.Auto.ESeg.eval_agree (n := n) (fa := fa) (fb := fb) (hp := hp)

end

section
-- from Silmaril/Proofs/Wasm/Auto/ESeg/LogicS.lean

open Silmaril.Wasm Silmaril.Wasm.Auto
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec localVal?)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec Silmaril.Wasm.Auto.ESeg

/-- The every-run weakest precondition of a typed body: its end or its trap. -/
theorem wp_typed {H : Type} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {Γ : List IntType} {a : List Instr} {s : Store H} {f : Frame} {us : List Val}
    {st : List IntType} (ht : tsteps Γ [] a = some st) (hf : LocalsOk Γ f) :
    (∃ f' rs', execS s f us.reverse a = some (s, f', rs') ∧ f'.module = f.module ∧
        (Wp m P host s f (vals us ++ expression a ++ []) Q ↔ Q s f' (.normal rs'.reverse))) ∨
      (∃ f', execS s f us.reverse a = none ∧ f'.module = f.module ∧
        (Wp m P host s f (vals us ++ expression a ++ []) Q ↔ Q s f' .trap)) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.wp_typed (H := H) (m := m) (P := P) (host := host) (Q := Q) (Γ := Γ)
    (a := a) (s := s) (f := f) (us := us) (st := st) (ht := ht) (hf := hf)

/-- **Typed bodies with the same `execS` results up to the locals** have the same every-run
weakest precondition for every postcondition blind to the locals. -/
theorem wp_iff_of_outEq {H : Type} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {Γa Γb : List IntType} {a b : List Instr} {s : Store H} {fa fb : Frame}
    {us : List Val} {sta stb : List IntType} (hta : tsteps Γa [] a = some sta)
    (htb : tsteps Γb [] b = some stb) (hfa : LocalsOk Γa fa) (hfb : LocalsOk Γb fb)
    (hmod : fa.module = fb.module) (h : OutEq (execS s fa us.reverse a) (execS s fb us.reverse b))
    (hQ : Silmaril.Wasm.Auto.Equiv.LocalsBlind Q) :
    Wp m P host s fa (vals us ++ expression a ++ []) Q ↔
      Wp m P host s fb (vals us ++ expression b ++ []) Q :=
  Silmaril.Proofs.Wasm.Auto.ESeg.wp_iff_of_outEq (H := H) (m := m) (P := P) (host := host) (Q := Q)
    (Γa := Γa) (Γb := Γb) (a := a) (b := b) (s := s) (fa := fa) (fb := fb) (us := us) (sta := sta)
    (stb := stb) (hta := hta) (htb := htb) (hfa := hfa) (hfb := hfb) (hmod := hmod) (h := h)
    (hQ := hQ)

end

end Silmaril.Wasm.Auto.ESeg

namespace Silmaril.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec

variable {f : Frame}

theorem len_le_of_frameOk {Γ : List IntType} (hl : Γ.length < 2 ^ 32) (hf : FrameOk Γ f) :
    Γ.length ≤ f.locals.length :=
  Silmaril.Proofs.Wasm.Auto.ESeg.len_le_of_frameOk hl hf

/-- **Soundness of the segment checker with `select`.** -/
theorem segEquivSel_of_checkSegSel {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkSegSel Γ rules a b c = true) :
    SegEquivSel Γ a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.segEquivSel_of_checkSegSel c hR h

/-- **Soundness of the body checker with `select`.** -/
theorem bodyEquivSel_of_checkBodySel {Γ : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkBodySel Γ rules a b c = true) :
    BodyEquivSel Γ a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.bodyEquivSel_of_checkBodySel c hR h

/-- **Soundness of the function checker.** -/
theorem funcEquiv_of_checkFunc {Γ da db : List IntType} {rules : List Rule} {a b : List Instr}
    (c : SegCert) (hR : ∀ r ∈ rules, r.Sound) (h : checkFunc Γ da db rules a b c = true) :
    FuncEquiv Γ da db a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.funcEquiv_of_checkFunc c hR h

theorem selTerm_eval {a b c : Term} {x y k : BitVec 32} (ha : a.eval f = some (Val.i32 x))
    (hb : b.eval f = some (Val.i32 y)) (hc : c.eval f = some (Val.i32 k)) :
    (selTerm a b c).eval f = some (if k = 0 then Val.i32 y else Val.i32 x) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.selTerm_eval ha hb hc

/-- **Lifting with `select` is sound.** -/
theorem liftSel_exec {Γ : List IntType} {a : List Instr} {A : Sym} (hl : Γ.length < 2 ^ 32)
    (h : liftSel Γ a = some A) {H : Type} (s : Store H) (rs : List Val) (hf : FrameOk Γ f) :
    execS s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.liftSel_exec hl h s rs hf

theorem den_entry {Γ ds : List IntType} (hl : (Γ ++ ds).length < 2 ^ 32)
    (hf : EntryFrame Γ ds f) : den f (Sym.entry Γ.length ds) = some (f, []) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.den_entry hl hf

/-- **Lifting from function entry is sound.** -/
theorem liftEntrySel_exec {Γ ds : List IntType} {a : List Instr} {A : Sym}
    (hl : (Γ ++ ds).length < 2 ^ 32) (h : liftEntrySel Γ ds a = some A) {H : Type} (s : Store H)
    (rs : List Val) (hf : EntryFrame Γ ds f) :
    execS s f rs a = (den f A).map fun p => (s, p.1, p.2 ++ rs) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.liftEntrySel_exec hl h s rs hf

end Silmaril.Wasm.Auto.ESeg

namespace Silmaril.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec_sound Post localVal?)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.EGraph

variable {H : Type}

theorem codeAt_init (lt : List IntType) (ρ : Equiv.Env) (us : List Val) (a : List Instr)
    (rest : List Admin) :
    Equiv.codeAt ρ (Equiv.initState lt []) us a rest = vals us ++ expression a ++ rest :=
  Silmaril.Proofs.Wasm.Auto.ESeg.codeAt_init lt ρ us a rest

/-- **A typed, trap-free segment runs** in every frame typed by `Γ`. -/
theorem pure_runs {Γ : List IntType} {a : List Instr} (ha : checkPure Γ a = true) (s : Store H)
    {f : Frame} (rs : List Val) (hf : FrameOk Γ f) : ∃ r, exec s f rs a = some r :=
  Silmaril.Proofs.Wasm.Auto.ESeg.pure_runs ha s rs hf

/-- **Code that `exec` runs** has the weakest precondition of its result. -/
theorem wp_exec_iff {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {s s' : Store H} {f f' : Frame} {vs rs' : List Val} {a : List Instr} (rest : List Admin)
    (he : exec s f vs.reverse a = some (s', f', rs')) :
    Wp m P host s f (vals vs ++ expression a ++ rest) Q ↔
      Wp m P host s' f' (vals rs'.reverse ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.ESeg.wp_exec_iff rest he

theorem frameOk_frameAt {lt : List IntType} (hl : lt.length < 2 ^ 32) (f : Frame)
    (ρ : Equiv.Env) : FrameOk lt (Equiv.frameAt f ρ (Equiv.initState lt [])) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.frameOk_frameAt hl f ρ

/-- Values satisfy the weakest precondition exactly when they satisfy the normal
postcondition. -/
theorem wp_vals_iff {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {s : Store H} {f : Frame} {vs : List Val} :
    Wp m P host s f (vals vs) Q ↔ Q s f (.normal vs) :=
  Silmaril.Proofs.Wasm.Auto.ESeg.wp_vals_iff

/-- **Segment equivalence in the every-run logic**: typed, trap-free segments that are
exec-equivalent on frames typed by `Γ` have the same every-run weakest precondition in every
context (the second segment then runs too). -/
theorem equivSeg_of_segEquiv {Γ : List IntType} {a b : List Instr} (h : SegEquiv Γ a b)
    (ha : checkPure Γ a = true) : Equiv.SegEquiv Γ [] a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.equivSeg_of_segEquiv h ha

/-- **Function bodies in the every-run logic**: typed, trap-free bodies that are equivalent up
to their locals have the same every-run weakest precondition for every postcondition blind to
the locals (such as `funcPost` and `bodyPost` of the call rules). -/
theorem outEquiv_of_bodyEquiv {Γ : List IntType} {a b : List Instr} (h : BodyEquiv Γ a b)
    (ha : checkPure Γ a = true) (hb : checkPure Γ b = true) : Equiv.OutEquiv Γ [] a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.outEquiv_of_bodyEquiv h ha hb

end Silmaril.Wasm.Auto.ESeg

namespace Silmaril.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg

/-- `local.set 1; local.get 1` is `local.tee 1` in the every-run logic (from the e-graph
certificate of `Silmaril.Wasm.Auto.ESeg.Tests.tee_form`, restated here). -/
theorem tee_form_everyRun :
    Silmaril.Wasm.Auto.Equiv.SegEquiv [.i32, .i32] []
      [.localGet (lidx 0), .intConst .i32 1, .intBinOp .i32 .add, .localSet (lidx 1),
        .localGet (lidx 1)]
      [.localGet (lidx 0), .intConst .i32 1, .intBinOp .i32 .add, .localTee (lidx 1)] :=
  equivSeg_of_segEquiv
    (segEquiv_of_checkSeg
      { stack := [[]], locs := [[], []], covA := [.total, .total, .total, .total],
        covB := [.total, .total, .total, .total] } Silmaril.Wasm.Auto.Rules.library_sound
      (by decide +kernel))
    (by decide +kernel)

end Silmaril.Wasm.Auto.ESeg

namespace Silmaril.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Post exec localVal?)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Auto.EGraph Silmaril.Wasm.Auto.ESeg Silmaril.Wasm.Auto.XExec Silmaril.Wasm.Auto.ESeg

variable {H : Type} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}

/-- **Bodies with `select`, traps included, in the every-run logic.** -/
theorem outEquivSel_of_bodyEquivSel {Γ : List IntType} {a b : List Instr} (h : BodyEquivSel Γ a b)
    (ha : typedBody Γ a = true) (hb : typedBody Γ b = true) :
    Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.outEquivSel_of_bodyEquivSel h ha hb

/-- **`select`-free bodies, traps included, in the every-run logic.** -/
theorem outEquiv_of_bodyEquiv_typed {Γ : List IntType} {a b : List Instr} (h : BodyEquiv Γ a b)
    (ha : noSelect a && typedBody Γ a = true) (hb : noSelect b && typedBody Γ b = true) :
    Silmaril.Wasm.Auto.Equiv.OutEquiv Γ [] a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.outEquiv_of_bodyEquiv_typed h ha hb

/-- **Segments with `select`, without division, in the every-run logic.** -/
theorem equivSeg_of_segEquivSel {Γ : List IntType} {a b : List Instr} (h : SegEquivSel Γ a b)
    (ha : typedBody Γ a && noDiv a = true) : Silmaril.Wasm.Auto.Equiv.SegEquiv Γ [] a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.equivSeg_of_segEquivSel h ha

/-- **Function bodies with different declared locals in the every-run logic**, traps
included. -/
theorem funcOutEquiv_of_funcEquiv {Γ da db : List IntType} {a b : List Instr}
    (h : FuncEquiv Γ da db a b) (ha : typedBody (Γ ++ da) a = true)
    (hb : typedBody (Γ ++ db) b = true) : FuncOutEquiv Γ da db a b :=
  Silmaril.Proofs.Wasm.Auto.ESeg.funcOutEquiv_of_funcEquiv h ha hb

end Silmaril.Wasm.Auto.ESeg
