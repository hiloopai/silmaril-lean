module

public import Silmaril.Wasm.Auto.Equiv.Defs
public import Mathlib.Data.BitVec
public import Mathlib.Tactic.Ring
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Logic.Instr.Thms
public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.Memory.Thms
import Silmaril.Proofs.Wasm.Auto.Equiv.Ext.Check

/-!
# Automatic equivalence of Wasm code: soundness

## Straight-line segments

For the checker of `Silmaril.Wasm.Auto.Equiv.Defs` (proofs in
`Silmaril/Proofs/Wasm/Auto/Equiv/{Norm,Sexec,Check,Typed,Basic}`):

* `ev_norm`: the normaliser preserves values; `safeBin_ok`: admitted divisions and
  remainders do not trap;
* `sexec_exec`: symbolic execution agrees with the straight-line interpreter
  `Silmaril.Wasm.Logic.Core.exec` (itself proved against silmaril-lean's small-step
  semantics by `exec_sound`);
* `wp_sexec_iff`: the every-run weakest precondition (`HWP` and `TWP`, every
  profile and host relation) of a symbolically executed segment is that of its final
  symbolic state;
* **`segEquiv_of_check`**: `check lt st a b = true → SegEquiv lt st a b`
  (`Silmaril.Proofs.Wasm.Auto.Equiv.Check`);
* `segEquiv_of_residuals`: equal shapes and proofs of the residual bitvector goals
  (`Goal.Holds`) give `SegEquiv`;
* **`not_segEquiv_of_cex`**: a counterexample environment (`cexAt … = true`, found by
  `findCex`'s differential testing and checked by `decide`) refutes `SegEquiv`;
* `outEquiv_of_checkOut`, `outEquiv_of_residualsOut`, `not_outEquiv_of_cex`: the same
  for `OutEquiv`, the equivalence of results (scratch locals ignored), for segments that
  end a function body;
* `SegEquiv.typed`, `OutEquiv.typed`: the equivalences on every typed concrete
  configuration (locals and stack top of the input types), the form an optimizer proof
  uses with the typing that validation provides;
* `SegEquiv.refl`, `SegEquiv.symm`, `SegEquiv.trans`; `SegEquiv.body`: equivalent
  function bodies (empty initial stack) have the same weakest precondition for every
  postcondition, in particular for the function postconditions of the call rules.

## Code in context

For the notions of `Silmaril.Wasm.Auto.Equiv.Defs` (proofs in
`Silmaril/Raw/Wasm/Auto/Equiv/Ctl/Inv`, `Silmaril/Proofs/Wasm/Auto/Equiv/Ctl/{Congr,Loop}`):

**The sequencing and label rules are equivalences** (both readings of the every-run logic):

* `hwp_seq_inv`, `twp_seq_inv`, `wp_seq_iff`: `Wp (c₁ ++ c₂) Q ↔ Wp c₁ (seqPostM c₂ Q)`;
* `hwp_label_inv`, `twp_label_inv`, `wp_label_iff`: `Wp (val* LABEL_k{cont} b) Q ↔
  Wp b (labelPostM k cont us Q)` when the value below the label is not a function reference
  (`NoFuncTop`);
* `wp_plug_iff`: code in a label context `E` has the weakest precondition of the code with the
  postcondition `E.post`;
* `wp_block_iff`, `wp_if_iff`, `wp_brIf_frame`: one step of `block` (no parameters), `if` and
  `br_if`.

**Equivalence in typed contexts** (`CEquiv`, both readings; `PEquiv`, partial correctness):

* `SegEquiv.cequiv`: the straight-line checker's `SegEquiv` (`Silmaril.Wasm.Auto.Equiv`) gives
  `CEquiv`; `CEquiv.plug`: in every label context;
* `CEquiv.refl`, `symm`, `trans`, `part`;
* `CEquiv.append`: sequential composition on the right; `CEquiv.prepend`: on the left, after
  code whose normal exits are typed (`Keeps`; `Keeps.brIf`, `Keeps.of_sexec`, `Keeps.append`),
  which gives the congruence **under `br_if`**;
* **`CEquiv.block`**, **`CEquiv.if_`**: congruence under `block` and `if` (block types without
  parameters, `NoParams`);
* **`CEquiv.loop`**: congruence under `loop` for partial correctness, by **Löb induction** on the
  step index of `HWP` (`safe_loop_congr`): the two loops run in lockstep, iteration by
  iteration, when the body keeps the locals typed at its back edges (`KeepsBr0`;
  `KeepsBr0.of_check` decides it for `do … while` bodies `c ++ [br_if l]` with straight-line
  `c`; `KeepsBr0.of_cequiv` transfers it).

## The extended language

For the checker of `Silmaril.Wasm.Auto.Equiv.Defs` (proofs in
`Silmaril/Proofs/Wasm/Auto/Equiv/Ext/{Canon,Store,Step,Check}`, `Silmaril/Raw/Wasm/Auto/Equiv/Ext/Run`):

* `evX_canon`, `evM_canonM`, `holds_canon`: the simplifier preserves values (`Equiv.norm` on
  pure integer subterms, oriented comparisons, ordered commutative operators, `select` with a
  constant or equal branches, `wrap` of `extend`, constant conversions);
* `wp_det_iff`: a deterministic head step does not change the every-run weakest precondition;
  `wp_xstep`: one symbolic step, every supported instruction, with the trap outcome when the
  step's guard fails (division by zero or overflow, out-of-bounds load or store);
* `wp_xsexec`: a symbolic run; `XOut`: the trap postcondition at the first failing guard, or the
  final configuration;
* **`segEquivX_of_checkX`**: the equivalence check is sound (`SegEquivX`, both readings, every
  profile and host relation, every typed context with locals, stack top and globals of the
  given types and memory `0` when `mem`);
* **`outEquivX_of_checkOutX`**: the result check for function bodies (`OutEquivX`, scratch
  locals ignored, postconditions blind to the locals);
* **`segRefinesX_of_refinesX`**: **refinement**: whatever the right side guarantees, the left
  side guarantees or traps (`TrapOr`), when every guard of the right side is a guard of the left
  side and the final states agree — trapping code refined by code that traps at most where it
  does;
* `SegEquivX.cequiv`: without globals and memory, `SegEquivX` gives `Equiv.CEquiv`, so the
  congruence rules for `block`, `if`, `br_if` and `loop` (`Silmaril.Wasm.Auto.Equiv.Thms`)
  apply.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Equiv

/-! ## Results proved in `Silmaril.Proofs.Wasm.Auto.Equiv` -/

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Norm.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv.Lin

@[simp] theorem binV_add (t : IntType) (x y : BitVec t.width) : binV t .add x y = x + y :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_add (t := t) (x := x) (y := y)

@[simp] theorem binV_sub (t : IntType) (x y : BitVec t.width) : binV t .sub x y = x - y :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_sub (t := t) (x := x) (y := y)

@[simp] theorem binV_mul (t : IntType) (x y : BitVec t.width) : binV t .mul x y = x * y :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_mul (t := t) (x := x) (y := y)

@[simp] theorem binV_and (t : IntType) (x y : BitVec t.width) : binV t .and x y = (x &&& y) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_and (t := t) (x := x) (y := y)

theorem binV_shrU (t : IntType) (x y : BitVec t.width) :
    binV t (.shr .unsigned) x y = x >>> (y.toNat % t.width) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_shrU (t := t) (x := x) (y := y)

theorem binV_divU {t : IntType} {x y : BitVec t.width} (hy : y ≠ 0#t.width) :
    binV t (.div .unsigned) x y = x / y :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_divU (t := t) (x := x) (y := y) (hy := hy)

theorem binV_remU {t : IntType} {x y : BitVec t.width} (hy : y ≠ 0#t.width) :
    binV t (.rem .unsigned) x y = x % y :=
  Silmaril.Proofs.Wasm.Auto.Equiv.binV_remU (t := t) (x := x) (y := y) (hy := hy)

/-- **The normaliser preserves values.** -/
theorem ev_norm {ρ : Env} (t : IntType) (e : Term) : ev ρ t (norm t e) = ev ρ t e :=
  Silmaril.Proofs.Wasm.Auto.Equiv.ev_norm (ρ := ρ) (t := t) (e := e)

theorem remU_ok (t : IntType) (x y : BitVec t.width) (hy : y ≠ 0#t.width) :
    ∃ z, intBinOp t (.rem .unsigned) x y = .ok z :=
  Silmaril.Proofs.Wasm.Auto.Equiv.remU_ok (t := t) (x := x) (y := y) (hy := hy)

/-- An admitted division or remainder does not trap. -/
theorem safeBin_ok {ρ : Env} (t : IntType) (op : IntBinOp) (b : Term) (hs : safeBin t op b = true)
    (x : BitVec t.width) : ∃ z, intBinOp t op x (ev ρ t b) = .ok z :=
  Silmaril.Proofs.Wasm.Auto.Equiv.safeBin_ok (ρ := ρ) (t := t) (op := op) (b := b) (hs := hs) (x := x)

end

section
-- from Silmaril/Raw/Wasm/Auto/Equiv/Step.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 popInt popV localVal? Post)
open Silmaril.Wasm.Logic.Hoare

theorem frameAt_stack {ρ : Env} (f : Frame) (ls st st' : List (IntType × Term)) :
    frameAt f ρ ⟨ls, st⟩ = frameAt f ρ ⟨ls, st'⟩ :=
  Silmaril.Proofs.Wasm.Auto.Equiv.frameAt_stack (ρ := ρ) (f := f) (ls := ls) (st := st) (st' := st')

/-- **Forward rule** for one symbolic step. -/
theorem wp_sstep {H : Type} {ρ : Env} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {S S' : SState} {i : Instr} (h : sstep S i = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin)
    (hw : Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q) :
    Wp m P host s (frameAt f ρ S) (vals (us ++ (stackAt ρ S).reverse) ++ .plain i :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_sstep (H := H) (ρ := ρ) (m := m) (P := P) (host := host) (Q := Q)
    (S := S) (S' := S') (i := i) (h := h) (s := s) (f := f) (us := us) (rest := rest) (hw := hw)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Sexec.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (exec exec1 popInt popV localVal? exec_sound Post)
open Silmaril.Wasm.Logic.Hoare

/-- **A symbolic run is a run of `exec`.** -/
theorem sexec_exec {H : Type} {ρ : Env} {S S' : SState} {a : List Instr} (h : sexec S a = some S')
    (s : Store H)
    (f : Frame) (extra : List Val) :
    exec s (frameAt f ρ S) (stackAt ρ S ++ extra) a =
      some (s, frameAt f ρ S', stackAt ρ S' ++ extra) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.sexec_exec (H := H) (ρ := ρ) (S := S) (S' := S') (a := a) (h := h)
    (s := s) (f := f) (extra := extra)

theorem wp_steps_inv {H : Type} {m : Corr} {P : Profile} {host : HostSemantics H} {Q : Post H}
    {c c' : Config H} (hs : Steps P host c c') (h : Wp m P host c.store c.frame c.code Q) :
    Wp m P host c'.store c'.frame c'.code Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_steps_inv (H := H) (m := m) (P := P) (host := host) (Q := Q)
    (c := c) (c' := c') (hs := hs) (h := h)

/-- **The weakest precondition of a symbolically executed segment** is that of its
final symbolic state, in both readings, for every profile, host relation, context and
postcondition. -/
theorem wp_sexec_iff {H : Type} {ρ : Env} {m : Corr} {P : Profile} {host : HostSemantics H}
    {Q : Post H}
    {S S' : SState} {a : List Instr} (h : sexec S a = some S') (s : Store H) (f : Frame)
    (us : List Val) (rest : List Admin) :
    Wp m P host s (frameAt f ρ S) (codeAt ρ S us a rest) Q ↔
      Wp m P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_sexec_iff (H := H) (ρ := ρ) (m := m) (P := P) (host := host)
    (Q := Q) (S := S) (S' := S') (a := a) (h := h) (s := s) (f := f) (us := us) (rest := rest)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Check.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare

theorem map_den_of_slotsEq {ρ : Env} : ∀ {ps qs : List (IntType × Term)}, slotsEq ps qs = true →
    ps.map (den ρ) = qs.map (den ρ) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.map_den_of_slotsEq (ρ := ρ)

theorem map_den_of_slotsGoals {ρ : Env} : ∀ {ps qs : List (IntType × Term)} {gs : List Goal},
    slotsGoals ps qs = some gs → (∀ g ∈ gs, g.Holds) → ps.map (den ρ) = qs.map (den ρ) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.map_den_of_slotsGoals (ρ := ρ)

/-- **The equivalence checker is sound.** -/
theorem segEquiv_of_check {lt st : List IntType} {a b : List Instr}
    (h : check lt st a b = true) : SegEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.segEquiv_of_check (lt := lt) (st := st) (a := a) (b := b) (h := h)

/-- **Residual goals.** Two segments with the same shape and types are equivalent once
the residual bitvector goals are proved. -/
theorem segEquiv_of_residuals {lt st : List IntType} {a b : List Instr} {gs : List Goal}
    (h : residuals lt st a b = some gs) (hg : ∀ g ∈ gs, g.Holds) : SegEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.segEquiv_of_residuals (lt := lt) (st := st) (a := a) (b := b)
    (gs := gs) (h := h) (hg := hg)

theorem wp_vals_iff {m : Corr} {P : Profile} {H : Type} {host : HostSemantics H}
    {Q : Silmaril.Wasm.Logic.Core.Post H} (s : Store H) (F : Frame) (vs : List Val) :
    Wp m P host s F (vals vs) Q ↔ Q s F (.normal vs) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_vals_iff (m := m) (P := P) (H := H) (host := host) (Q := Q)
    (s := s) (F := F) (vs := vs)

/-- **The result check is sound.** -/
theorem outEquiv_of_checkOut {lt st : List IntType} {a b : List Instr}
    (h : checkOut lt st a b = true) : OutEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.outEquiv_of_checkOut (lt := lt) (st := st) (a := a) (b := b) (h := h)

/-- Residual goals for the result check. -/
theorem outEquiv_of_residualsOut {lt st : List IntType} {a b : List Instr} {gs : List Goal}
    (h : residualsOut lt st a b = some gs) (hg : ∀ g ∈ gs, g.Holds) : OutEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.outEquiv_of_residualsOut (lt := lt) (st := st) (a := a) (b := b)
    (gs := gs) (h := h) (hg := hg)

/-- **Refutation by a counterexample.** An environment in which the two final states
differ refutes `SegEquiv`. -/
theorem not_segEquiv_of_cex {lt st : List IntType} {a b : List Instr} (ρ : Env)
    (h : cexAt lt st a b ρ = true) : ¬ SegEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.not_segEquiv_of_cex (lt := lt) (st := st) (a := a) (b := b) (ρ := ρ)
    (h := h)

/-- **Refutation of results by a counterexample.** -/
theorem not_outEquiv_of_cex {lt st : List IntType} {a b : List Instr} (ρ : Env)
    (h : cexAtOut lt st a b ρ = true) : ¬ OutEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.not_outEquiv_of_cex (lt := lt) (st := st) (a := a) (b := b) (ρ := ρ)
    (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Typed.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

theorem map_den_envOfVals {ts : List IntType} {vs : List Val} (htv : TypedVals ts vs)
    (rest more : List Val) :
    (ts.mapIdx fun i t => (t, Term.var (rest.length + i))).map
      (den (envOfVals (rest ++ vs ++ more))) = vs :=
  Silmaril.Proofs.Wasm.Auto.Equiv.map_den_envOfVals (ts := ts) (vs := vs) (htv := htv) (rest := rest)
    (more := more)

/-- **`SegEquiv` on typed concrete states.** -/
theorem SegEquiv.typed {lt st : List IntType} {a b : List Instr} (h : SegEquiv lt st a b)
    (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) {f : Frame}
    {ls rs : List Val} (hf : f.locals = ls.map some) (hl : TypedVals lt ls)
    (hs : TypedVals st rs) (us : List Val) (rest : List Admin)
    (Q : Silmaril.Wasm.Logic.Core.Post H) :
    Wp m P host s f (vals (us ++ rs.reverse) ++ expression a ++ rest) Q ↔
      Wp m P host s f (vals (us ++ rs.reverse) ++ expression b ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.typed (lt := lt) (st := st) (a := a) (b := b) (h := h)
    (m := m) (P := P) (H := H) (host := host) (s := s) (f := f) (ls := ls) (rs := rs) (hf := hf)
    (hl := hl) (hs := hs) (us := us) (rest := rest) (Q := Q)

/-- **`OutEquiv` on typed concrete states.** -/
theorem OutEquiv.typed {lt st : List IntType} {a b : List Instr} (h : OutEquiv lt st a b)
    (m : Corr) (P : Profile) {H : Type} (host : HostSemantics H) (s : Store H) {f : Frame}
    {ls rs : List Val} (hf : f.locals = ls.map some) (hl : TypedVals lt ls)
    (hs : TypedVals st rs) (us : List Val) (Q : Silmaril.Wasm.Logic.Core.Post H)
    (hQ : LocalsBlind Q) :
    Wp m P host s f (vals (us ++ rs.reverse) ++ expression a) Q ↔
      Wp m P host s f (vals (us ++ rs.reverse) ++ expression b) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.OutEquiv.typed (lt := lt) (st := st) (a := a) (b := b) (h := h)
    (m := m) (P := P) (H := H) (host := host) (s := s) (f := f) (ls := ls) (rs := rs) (hf := hf)
    (hl := hl) (hs := hs) (us := us) (Q := Q) (hQ := hQ)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Basic.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare (Wp Corr)

theorem SegEquiv.refl (lt st : List IntType) (a : List Instr) : SegEquiv lt st a a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.refl (lt := lt) (st := st) (a := a)

theorem SegEquiv.symm {lt : List IntType} {st : List IntType} {a : List Instr} {b : List Instr}
    (h : SegEquiv lt st a b) : SegEquiv lt st b a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.symm (lt := lt) (st := st) (a := a) (b := b) (h := h)

theorem SegEquiv.trans {lt : List IntType} {st : List IntType} {a : List Instr} {b : List Instr}
    {c : List Instr} (h₁ : SegEquiv lt st a b) (h₂ : SegEquiv lt st b c) : SegEquiv lt st a c :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.trans (lt := lt) (st := st) (a := a) (b := b) (c := c)
    (h₁ := h₁) (h₂ := h₂)

theorem OutEquiv.refl (lt st : List IntType) (a : List Instr) : OutEquiv lt st a a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.OutEquiv.refl (lt := lt) (st := st) (a := a)

theorem OutEquiv.symm {lt : List IntType} {st : List IntType} {a : List Instr} {b : List Instr}
    (h : OutEquiv lt st a b) : OutEquiv lt st b a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.OutEquiv.symm (lt := lt) (st := st) (a := a) (b := b) (h := h)

theorem OutEquiv.trans {lt : List IntType} {st : List IntType} {a : List Instr} {b : List Instr}
    {c : List Instr} (h₁ : OutEquiv lt st a b) (h₂ : OutEquiv lt st b c) : OutEquiv lt st a c :=
  Silmaril.Proofs.Wasm.Auto.Equiv.OutEquiv.trans (lt := lt) (st := st) (a := a) (b := b) (c := c)
    (h₁ := h₁) (h₂ := h₂)

/-- `SegEquiv` implies `OutEquiv`. -/
theorem SegEquiv.out {lt : List IntType} {st : List IntType} {a : List Instr} {b : List Instr}
    (h : SegEquiv lt st a b) : OutEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.out (lt := lt) (st := st) (a := a) (b := b) (h := h)

/-- **Function bodies.** Equivalent straight-line bodies (locals typed `lt`, empty
initial stack) have the same every-run weakest precondition for every postcondition. -/
theorem SegEquiv.body {lt : List IntType} {a : List Instr} {b : List Instr} (h : SegEquiv lt [] a b)
    (m : Corr) (P : Profile) {H : Type}
    (host : HostSemantics H) (s : Store H) (f : Frame) (ρ : Env)
    (Q : Silmaril.Wasm.Logic.Core.Post H) :
    Wp m P host s (frameAt f ρ (initState lt [])) (expression a) Q ↔
      Wp m P host s (frameAt f ρ (initState lt [])) (expression b) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.body (lt := lt) (a := a) (b := b) (h := h) (m := m) (P := P)
    (H := H) (host := host) (s := s) (f := f) (ρ := ρ) (Q := Q)

end

section
-- from Silmaril/Raw/Wasm/Auto/Equiv/Ctl/Inv.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

/-- An exit of `c₁ ++ c₂` whose first part is not all values is an exit of `c₁`. -/
theorem Exits.of_append {o : Outcome} {c₁ c₂ : List Admin} (hna : c₁.all Admin.isVal = false)
    (h : Exits o (c₁ ++ c₂)) : Exits o c₁ :=
  Silmaril.Proofs.Wasm.Auto.Equiv.Exits.of_append (o := o) (c₁ := c₁) (c₂ := c₂) (hna := hna) (h := h)

theorem hwp_seq_inv {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {c₁ c₂ : List Admin} {Q : Post H}
    (h : HWP P host s f (c₁ ++ c₂) Q) : HWP P host s f c₁ (seqPost P host c₂ Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.hwp_seq_inv (H := H) (P := P) (host := host) (s := s) (f := f)
    (c₁ := c₁) (c₂ := c₂) (Q := Q) (h := h)

theorem twp_seq_inv {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {c₁ c₂ : List Admin} {Q : Post H}
    (h : TWP P host s f (c₁ ++ c₂) Q) : TWP P host s f c₁ (seqPostT P host c₂ Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.twp_seq_inv (H := H) (P := P) (host := host) (s := s) (f := f)
    (c₁ := c₁) (c₂ := c₂) (Q := Q) (h := h)

theorem wp_step_inv {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s s' : Store H}
    {f f' : Frame} {c c' : List Admin} {Q : Post H}
    (h : Wp m P host s f c Q) (hst : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) :
    Wp m P host s' f' c' Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_step_inv (H := H) (P := P) (host := host) (m := m) (s := s)
    (s' := s') (f := f) (f' := f') (c := c) (c' := c') (Q := Q) (h := h) (hst := hst)

theorem wp_exit_post {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {c : List Admin} {Q : Post H}
    {o : Outcome} (h : Wp m P host s f c Q) (he : Exits o c) : Q s f o :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_exit_post (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (c := c) (Q := Q) (o := o) (h := h) (he := he)

theorem hwp_label_inv {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {us : List Val} {k : Nat} {cont : List Instr}
    {b : List Admin} {Q : Post H} (hus : NoFuncTop us)
    (h : HWP P host s f (vals us ++ [.label k cont b]) Q) :
    HWP P host s f b (labelPost P host k cont us Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.hwp_label_inv (H := H) (P := P) (host := host) (s := s) (f := f)
    (us := us) (k := k) (cont := cont) (b := b) (Q := Q) (hus := hus) (h := h)

theorem twp_label_inv {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {us : List Val} {k : Nat} {cont : List Instr}
    {b : List Admin} {Q : Post H} (hus : NoFuncTop us)
    (h : TWP P host s f (vals us ++ [.label k cont b]) Q) :
    TWP P host s f b (labelPostT P host k cont us Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.twp_label_inv (H := H) (P := P) (host := host) (s := s) (f := f)
    (us := us) (k := k) (cont := cont) (b := b) (Q := Q) (hus := hus) (h := h)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ctl/Congr.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

theorem wp_mono {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {c : List Admin} {Q Q' : Post H}
    (hq : ∀ s f o, Q s f o → Q' s f o) (h : Wp m P host s f c Q) : Wp m P host s f c Q' :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_mono (H := H) (P := P) (host := host) (m := m) (s := s) (f := f)
    (c := c) (Q := Q) (Q' := Q') (hq := hq) (h := h)

theorem wp_seq_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {c₁ c₂ : List Admin} {Q : Post H} :
    Wp m P host s f (c₁ ++ c₂) Q ↔ Wp m P host s f c₁ (seqPostM m P host c₂ Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_seq_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (c₁ := c₁) (c₂ := c₂) (Q := Q)

theorem wp_label_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {us : List Val} {k : Nat}
    {cont : List Instr} {b : List Admin} {Q : Post H} (hus : NoFuncTop us) :
    Wp m P host s f (vals us ++ [.label k cont b]) Q ↔
      Wp m P host s f b (labelPostM m P host k cont us Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_label_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (us := us) (k := k) (cont := cont) (b := b) (Q := Q) (hus := hus)

/-- **Code in a label context.** -/
theorem wp_plug_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {x : List Admin} :
    ∀ {E : LCtx} {Q : Post H}, E.Ok →
      (Wp m P host s f (E.plug x) Q ↔ Wp m P host s f x (E.post m P host Q)) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_plug_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (x := x)

/-- The values below a typed stack top do not end with a function reference. -/
theorem noFuncTop_append {us rs : List Val} {st : List IntType} (hus : NoFuncTop us)
    (hrs : TypedVals st rs) : NoFuncTop (us ++ rs.reverse) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.noFuncTop_append (us := us) (rs := rs) (st := st) (hus := hus)
    (hrs := hrs)

/-- A `block` without parameters is its label. -/
theorem wp_block_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {us : List Val} {bt : BlockType}
    {a : List Instr} {rest : List Admin} {Q : Post H} {t₂ : List Validation.CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) (hus : NoFuncTop us) :
    Wp m P host s f (vals us ++ .plain (.block bt a) :: rest) Q ↔
      Wp m P host s f (vals us ++ [.label t₂.length [] (expression a)] ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_block_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (us := us) (bt := bt) (a := a) (rest := rest) (Q := Q) (t₂ := t₂) (hbt := hbt)
    (hus := hus)

/-- An `if` is the block of the taken branch. -/
theorem wp_if_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {us : List Val} {c : BitVec 32}
    {bt : BlockType} {b₁ b₂ : List Instr} {rest : List Admin} {Q : Post H} :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ .plain (.if_ bt b₁ b₂) :: rest) Q ↔
      Wp m P host s f (vals us ++ .plain (.block bt (if c ≠ 0 then b₁ else b₂)) :: rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_if_iff (H := H) (P := P) (host := host) (m := m) (s := s) (f := f)
    (us := us) (c := c) (bt := bt) (b₁ := b₁) (b₂ := b₂) (rest := rest) (Q := Q)

theorem TypedVals.tail {t : IntType} {ts : List IntType} {r : Val} {rs : List Val}
    (h : TypedVals (t :: ts) (r :: rs)) : TypedVals ts rs :=
  Silmaril.Proofs.Wasm.Auto.Equiv.TypedVals.tail (t := t) (ts := ts) (r := r) (rs := rs) (h := h)

theorem TypedVals.cons_inv {t : IntType} {ts : List IntType} {rs : List Val}
    (h : TypedVals (t :: ts) rs) : ∃ r rs', rs = r :: rs' :=
  Silmaril.Proofs.Wasm.Auto.Equiv.TypedVals.cons_inv (t := t) (ts := ts) (rs := rs) (h := h)

theorem CEquiv.refl (lt st : List IntType) (a : List Instr) : CEquiv lt st a a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.refl (lt := lt) (st := st) (a := a)

theorem CEquiv.symm {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b) :
    CEquiv lt st b a :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.symm (lt := lt) (st := st) (a := a) (b := b) (h := h)

theorem CEquiv.trans {lt st : List IntType} {a b c : List Instr} (h₁ : CEquiv lt st a b)
    (h₂ : CEquiv lt st b c) : CEquiv lt st a c :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.trans (lt := lt) (st := st) (a := a) (b := b) (c := c)
    (h₁ := h₁) (h₂ := h₂)

theorem CEquiv.part {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b) :
    PEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.part (lt := lt) (st := st) (a := a) (b := b) (h := h)

/-- **The straight-line checker's equivalence holds in typed contexts.** -/
theorem SegEquiv.cequiv {lt st : List IntType} {a b : List Instr} (h : SegEquiv lt st a b) :
    CEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquiv.cequiv (lt := lt) (st := st) (a := a) (b := b) (h := h)

/-- Equivalent code, in any label context. -/
theorem CEquiv.plug {H : Type} {P : Profile} {host : HostSemantics H} {lt st : List IntType}
    {a b : List Instr} (h : CEquiv lt st a b)
    {m : Corr} {s : Store H} {f : Frame} {rs us : List Val} {rest : List Admin} {E : LCtx}
    {Q : Post H} (hE : E.Ok) (hf : TypedFrame lt f) (hrs : TypedVals st rs) (hus : NoFuncTop us) :
    Wp m P host s f (E.plug (cfgCode us rs a rest)) Q ↔
      Wp m P host s f (E.plug (cfgCode us rs b rest)) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.plug (H := H) (P := P) (host := host) (lt := lt) (st := st)
    (a := a) (b := b) (h := h) (m := m) (s := s) (f := f) (rs := rs) (us := us) (rest := rest)
    (E := E) (Q := Q) (hE := hE) (hf := hf) (hrs := hrs) (hus := hus)

/-- **Sequential composition, right.** -/
theorem CEquiv.append {lt st : List IntType} {a b : List Instr} (h : CEquiv lt st a b)
    (c : List Instr) : CEquiv lt st (a ++ c) (b ++ c) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.append (lt := lt) (st := st) (a := a) (b := b) (h := h)
    (c := c)

theorem seqPostM_ne_normal {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr}
    {c : List Admin} {Q : Post H} {s : Store H} {F : Frame}
    {o : Outcome} (ho : ∀ vs, o ≠ .normal vs) : seqPostM m P host c Q s F o ↔ Q s F o :=
  Silmaril.Proofs.Wasm.Auto.Equiv.seqPostM_ne_normal (H := H) (P := P) (host := host) (m := m) (c := c)
    (Q := Q) (s := s) (F := F) (o := o) (ho := ho)

theorem seqPostM_normal {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr}
    {c : List Admin} {Q : Post H} {s : Store H} {F : Frame}
    {vs : List Val} : seqPostM m P host c Q s F (.normal vs) ↔ Wp m P host s F (vals vs ++ c) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.seqPostM_normal (H := H) (P := P) (host := host) (m := m) (c := c)
    (Q := Q) (s := s) (F := F) (vs := vs)

/-- **Sequential composition, left**, after code whose normal exits are typed. -/
theorem CEquiv.prepend {lt st lt' st' : List IntType} {c a b : List Instr}
    (hc : Keeps lt st c lt' st') (h : CEquiv lt' st' a b) : CEquiv lt st (c ++ a) (c ++ b) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.prepend (lt := lt) (st := st) (lt' := lt') (st' := st')
    (c := c) (a := a) (b := b) (hc := hc) (h := h)

/-- **`block`** (no parameters: `empty` or a value type). -/
theorem CEquiv.block {lt st : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂)) (h : CEquiv lt [] a b) :
    CEquiv lt st [.block bt a] [.block bt b] :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.block (lt := lt) (st := st) (a := a) (b := b) (bt := bt)
    (hbt := hbt) (h := h)

/-- **`if`** (no parameters). -/
theorem CEquiv.if_ {lt st : List IntType} {a₁ a₂ b₁ b₂ : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂)) (h₁ : CEquiv lt [] a₁ b₁)
    (h₂ : CEquiv lt [] a₂ b₂) : CEquiv lt (.i32 :: st) [.if_ bt a₁ a₂] [.if_ bt b₁ b₂] :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.if_ (lt := lt) (st := st) (a₁ := a₁) (a₂ := a₂) (b₁ := b₁)
    (b₂ := b₂) (bt := bt) (hbt := hbt) (h₁ := h₁) (h₂ := h₂)

/-- `br_if` pops an `i32` and keeps the frame. -/
theorem Keeps.brIf (lt st : List IntType) (l : LabelIdx) : Keeps lt (.i32 :: st) [.brIf l] lt st :=
  Silmaril.Proofs.Wasm.Auto.Equiv.Keeps.brIf (lt := lt) (st := st) (l := l)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ctl/Loop.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

theorem typedVals_nil : TypedVals [] [] :=
  Silmaril.Proofs.Wasm.Auto.Equiv.typedVals_nil

theorem TypedVals.cons {t : IntType} {ts : List IntType} {v : Val} {vs : List Val}
    (x : BitVec t.width) (hv : v = .num ⟨.int t, x⟩) (h : TypedVals ts vs) :
    TypedVals (t :: ts) (v :: vs) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.TypedVals.cons (t := t) (ts := ts) (v := v) (vs := vs) (x := x)
    (hv := hv) (h := h)

/-- Equivalent bodies on an empty stack, for any postcondition. -/
theorem CEquiv.body_iff {H : Type} {P : Profile} {host : HostSemantics H} {lt : List IntType}
    {a b : List Instr} (h : CEquiv lt [] a b)
    {m : Corr} {s : Store H} {f : Frame} {Q : Post H} (hf : TypedFrame lt f) :
    Wp m P host s f (expression a) Q ↔ Wp m P host s f (expression b) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.body_iff (H := H) (P := P) (host := host) (lt := lt) (a := a)
    (b := b) (h := h) (m := m) (s := s) (f := f) (Q := Q) (hf := hf)

/-- The typing fact at back edges transfers along `CEquiv`. -/
theorem KeepsBr0.of_cequiv {lt : List IntType} {a b : List Instr} (hk : KeepsBr0 lt a)
    (h : CEquiv lt [] a b) : KeepsBr0 lt b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.KeepsBr0.of_cequiv (lt := lt) (a := a) (b := b) (hk := hk) (h := h)

theorem loop_step {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {us : List Val} {bt : BlockType} {a : List Instr}
    {t₂ : List Validation.CValType} (ht : f.module.blockType? bt = some ([], t₂)) :
    Step P host ⟨s, f, vals us ++ [.plain (.loop bt a)]⟩
      ⟨s, f, vals us ++ [.label 0 [.loop bt a] (expression a)]⟩ :=
  Silmaril.Proofs.Wasm.Auto.Equiv.loop_step (H := H) (P := P) (host := host) (s := s) (f := f)
    (us := us) (bt := bt) (a := a) (t₂ := t₂) (ht := ht)

/-- **Löb induction for the loop congruence.** -/
theorem safe_loop_congr {H : Type} {P : Profile} {host : HostSemantics H} {lt : List IntType}
    {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) (n : Nat) :
    ∀ {s : Store H} {f : Frame} {us : List Val} {Q : Post H},
      TypedFrame lt f → NoFuncTop us → HWP P host s f (vals us ++ [.plain (.loop bt a)]) Q →
      Safe P host Q n ⟨s, f, vals us ++ [.plain (.loop bt b)]⟩ :=
  Silmaril.Proofs.Wasm.Auto.Equiv.safe_loop_congr (H := H) (P := P) (host := host) (lt := lt) (a := a)
    (b := b) (bt := bt) (hbt := hbt) (h := h) (hk := hk) (n := n)

/-- **Loops** (no parameters): equivalent bodies, typed at their back edges, give loops with
the same partial-correctness weakest precondition. -/
theorem CEquiv.loop {lt st : List IntType} {a b : List Instr} {bt : BlockType}
    (hbt : ∀ mi : ModuleInst, ∃ t₂, mi.blockType? bt = some ([], t₂))
    (h : CEquiv lt [] a b) (hk : KeepsBr0 lt a) :
    PEquiv lt st [.loop bt a] [.loop bt b] :=
  Silmaril.Proofs.Wasm.Auto.Equiv.CEquiv.loop (lt := lt) (st := st) (a := a) (b := b) (bt := bt)
    (hbt := hbt) (h := h) (hk := hk)

/-- Typing facts compose. -/
theorem Keeps.append {lt st lt' st' lt'' st'' : List IntType} {c d : List Instr}
    (hc : Keeps lt st c lt' st') (hd : Keeps lt' st' d lt'' st'') : Keeps lt st (c ++ d) lt'' st'' :=
  Silmaril.Proofs.Wasm.Auto.Equiv.Keeps.append (lt := lt) (st := st) (lt' := lt') (st' := st')
    (lt'' := lt'') (st'' := st'') (c := c) (d := d) (hc := hc) (hd := hd)

/-- **Symbolically executed straight-line code keeps typed states.** -/
theorem Keeps.of_sexec {lt st : List IntType} {c : List Instr} {S : SState}
    (h : sexec (initState lt st) c = some S) :
    Keeps lt st c (S.locals.map Prod.fst) (S.stack.map Prod.fst) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.Keeps.of_sexec (lt := lt) (st := st) (c := c) (S := S) (h := h)

/-- `br_if` keeps the frame. -/
theorem wp_brIf_frame {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {us : List Val} {c : BitVec 32}
    {l : LabelIdx} {Q : Post H} (hw : Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) Q) :
    Wp m P host s f (vals (us ++ [.i32 c]) ++ [.plain (.brIf l)]) (fun s' F o => Q s' F o ∧ F = f) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_brIf_frame (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (us := us) (c := c) (l := l) (Q := Q) (hw := hw)

/-- `KeepsBr0` from the decidable check `brIfBodyOk`. -/
theorem KeepsBr0.of_check {lt : List IntType} {c : List Instr} (l : LabelIdx)
    (h : brIfBodyOk lt c = true) : KeepsBr0 lt (c ++ [.brIf l]) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.KeepsBr0.of_check (lt := lt) (c := c) (l := l) (h := h)

theorem noParams_empty : NoParams .empty :=
  Silmaril.Proofs.Wasm.Auto.Equiv.noParams_empty

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ext/Canon.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem evX_canon {ρ : Env} {B0 : ByteArray} (t : IntType)
    (e : XT) : evX ρ B0 t (canon t e) = evX ρ B0 t e :=
  Silmaril.Proofs.Wasm.Auto.Equiv.evX_canon (ρ := ρ) (B0 := B0) (t := t) (e := e)

theorem evM_canonM {ρ : Env} {B0 : ByteArray} (e : XT) : evM ρ B0 (canonM e) = evM ρ B0 e :=
  Silmaril.Proofs.Wasm.Auto.Equiv.evM_canonM (ρ := ρ) (B0 := B0) (e := e)

theorem holds_canon {ρ : Env} {B0 : ByteArray} (g : Guard) : g.canon.holds ρ B0 = g.holds ρ B0 :=
  Silmaril.Proofs.Wasm.Auto.Equiv.holds_canon (ρ := ρ) (B0 := B0) (g := g)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ext/Store.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem globals_length_setGlobals {H : Type} : ∀ (s : Store H) (ga : List Nat) (vs : List Val),
    (setGlobals s ga vs).globals.length = s.globals.length :=
  Silmaril.Proofs.Wasm.Auto.Equiv.globals_length_setGlobals (H := H)

theorem setGlobal_setGlobal {H : Type} (s : Store H) (a : Nat) (v w : Val) :
    (s.setGlobal a v).setGlobal a w = s.setGlobal a w :=
  Silmaril.Proofs.Wasm.Auto.Equiv.setGlobal_setGlobal (H := H) (s := s) (a := a) (v := v) (w := w)

theorem setGlobals_setGlobal_not_mem
    {H : Type} : ∀ (s : Store H) (ga : List Nat) (vs : List Val) (a : Nat)
    (v : Val), a ∉ ga → (setGlobals s ga vs).setGlobal a v = setGlobals (s.setGlobal a v) ga vs :=
  Silmaril.Proofs.Wasm.Auto.Equiv.setGlobals_setGlobal_not_mem (H := H)

theorem XCtx.Ok.good {H : Type} {lt st gt : List IntType} {mem : Bool} {c : XCtx H}
    (h : c.Ok lt st gt mem) : c.Good mem :=
  Silmaril.Proofs.Wasm.Auto.Equiv.XCtx.Ok.good (H := H) (lt := lt) (st := st) (gt := gt) (mem := mem)
    (c := c) (h := h)

theorem frameOf_setLocal {H : Type} (c : XCtx H) (S : XState) (x : LocalIdx) (p : IntType × XT)
    (st : List (IntType × XT)) :
    c.frameOf { S with locals := S.locals.set x.toNat p, stack := st } =
      (c.frameOf S).setLocal x (denX c.ρ c.mi.bytes p) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.frameOf_setLocal (H := H) (c := c) (S := S) (x := x) (p := p)
    (st := st)

theorem mem?_storeOf {H : Type} {c : XCtx H} (hc : c.Good true) (S : XState) {x : MemIdx}
    (hx : x.toNat = 0) :
    (c.storeOf true S).mem? (c.frameOf S) x = some (c.ma, { c.mi with bytes := evM c.ρ c.mi.bytes S.mem }) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.mem?_storeOf (H := H) (c := c) (hc := hc) (S := S) (x := x)
    (hx := hx)

/-- Stores keep the size of memory. -/
theorem size_evM (ρ : Env) (B0 : ByteArray) : ∀ e : XT, (evM ρ B0 e).size = B0.size :=
  Silmaril.Proofs.Wasm.Auto.Equiv.size_evM (ρ := ρ) (B0 := B0)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ext/Step.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (Head famOf)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

theorem wp_det_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {f : Frame} {us args : List Val} {i : Instr}
    {rest : List Admin} {Q : Post H} {c₁ : Config H}
    (hfam : famOf (.plain i) ≠ .control) (hpf : ProfileFree i) (h₁ : Head P s f args (.plain i) c₁) :
    Wp m P host s f (vals (us ++ args) ++ .plain i :: rest) Q ↔
      Wp m P host c₁.store c₁.frame (vals us ++ c₁.code ++ rest) Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_det_iff (H := H) (P := P) (host := host) (m := m) (s := s)
    (f := f) (us := us) (args := args) (i := i) (rest := rest) (Q := Q) (c₁ := c₁) (hfam := hfam)
    (hpf := hpf) (h₁ := h₁)

theorem intBinOp_ok_of_safe {ρ : Env} {B0 : ByteArray} {t : IntType} {op : IntBinOp} {b : XT}
    (hs : safeBinX t op b = true) (x : BitVec t.width) :
    ∃ z, intBinOp t op x (evX ρ B0 t b) = .ok z :=
  Silmaril.Proofs.Wasm.Auto.Equiv.intBinOp_ok_of_safe (ρ := ρ) (B0 := B0) (t := t) (op := op) (b := b)
    (hs := hs) (x := x)

end

section
-- from Silmaril/Raw/Wasm/Auto/Equiv/Ext/Run.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

/-- **One symbolic step.** -/
theorem wp_xstep {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {mem : Bool}
    {c : XCtx H} (hc : c.Good mem) {S S' : XState}
    {i : Instr} (hl : S.globs.length = c.ga.length) (h : xstep mem S i = some S') (us : List Val)
    (rest : List Admin) (Q : Post H) :
    Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ .plain i :: rest) Q ↔
      XStepOut m P host c mem S S' us rest Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_xstep (H := H) (P := P) (host := host) (m := m) (mem := mem)
    (c := c) (hc := hc) (S := S) (S' := S') (i := i) (hl := hl) (h := h) (us := us) (rest := rest)
    (Q := Q)

end

section
-- from Silmaril/Proofs/Wasm/Auto/Equiv/Ext/Check.lean

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

theorem firstFail_append_some {ρ : Env} {B0 : ByteArray} {T : XState} :
    ∀ {G : List (Guard × XState)} (G' : List (Guard × XState)), firstFail ρ B0 G = some T →
      firstFail ρ B0 (G ++ G') = some T :=
  Silmaril.Proofs.Wasm.Auto.Equiv.firstFail_append_some (ρ := ρ) (B0 := B0) (T := T)

theorem xsexec_guards {mem : Bool} : ∀ {S S' : XState} {a : List Instr}, xsexec mem S a = some S' →
    ∃ G, S'.guards = S.guards ++ G :=
  Silmaril.Proofs.Wasm.Auto.Equiv.xsexec_guards (mem := mem)

theorem xsexec_globs {mem : Bool} : ∀ {S S' : XState} {a : List Instr}, xsexec mem S a = some S' →
    S'.globs.length = S.globs.length :=
  Silmaril.Proofs.Wasm.Auto.Equiv.xsexec_globs (mem := mem)

/-- **A symbolic run.** -/
theorem wp_xsexec {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {mem : Bool}
    {c : XCtx H} (hc : c.Good mem) (us : List Val)
    (rest : List Admin) (Q : Post H) :
    ∀ (a : List Instr) {S S' : XState}, S.globs.length = c.ga.length →
      firstFail c.ρ c.mi.bytes S.guards = none → xsexec mem S a = some S' →
      (Wp m P host (c.storeOf mem S) (c.frameOf S) (vals (us ++ (c.stackOf S).reverse) ++ expression a ++ rest) Q ↔
        XOut m P host c mem S' us rest Q) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_xsexec (H := H) (P := P) (host := host) (m := m) (mem := mem)
    (c := c) (hc := hc) (us := us) (rest := rest) (Q := Q)

theorem map_denX_canonSlots (ρ : Env) (B0 : ByteArray) (l : List (IntType × XT)) :
    (canonSlots l).map (denX ρ B0) = l.map (denX ρ B0) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.map_denX_canonSlots (ρ := ρ) (B0 := B0) (l := l)

theorem frameOf_eq_of_key {H : Type} (c : XCtx H) {S T : XState}
    (h : canonSlots S.locals = canonSlots T.locals) : c.frameOf S = c.frameOf T :=
  Silmaril.Proofs.Wasm.Auto.Equiv.frameOf_eq_of_key (H := H) (c := c) (S := S) (T := T) (h := h)

theorem storeOf_eq_of_key {H : Type} (c : XCtx H) (mem : Bool) {S T : XState}
    (hg : canonSlots S.globs = canonSlots T.globs) (hm : canonM S.mem = canonM T.mem) :
    c.storeOf mem S = c.storeOf mem T :=
  Silmaril.Proofs.Wasm.Auto.Equiv.storeOf_eq_of_key (H := H) (c := c) (mem := mem) (S := S) (T := T)
    (hg := hg) (hm := hm)

theorem stackOf_eq {H : Type} (c : XCtx H) {S T : XState}
    (h : canonSlots S.stack = canonSlots T.stack) :
    c.stackOf S = c.stackOf T :=
  Silmaril.Proofs.Wasm.Auto.Equiv.stackOf_eq (H := H) (c := c) (S := S) (T := T) (h := h)

theorem key_eq_parts {S T : XState} (h : S.key = T.key) :
    canonSlots S.locals = canonSlots T.locals ∧ canonSlots S.globs = canonSlots T.globs ∧
      canonM S.mem = canonM T.mem :=
  Silmaril.Proofs.Wasm.Auto.Equiv.key_eq_parts (S := S) (T := T) (h := h)

/-- Equal guard keys: the first failing guards correspond. -/
theorem firstFail_of_keys {ρ : Env} {B0 : ByteArray} :
    ∀ {G G' : List (Guard × XState)},
      G.map (fun g => (g.1.canon, g.2.key)) = G'.map (fun g => (g.1.canon, g.2.key)) →
      (firstFail ρ B0 G = none ∧ firstFail ρ B0 G' = none) ∨
        ∃ T T', firstFail ρ B0 G = some T ∧ firstFail ρ B0 G' = some T' ∧ T.key = T'.key :=
  Silmaril.Proofs.Wasm.Auto.Equiv.firstFail_of_keys (ρ := ρ) (B0 := B0)

/-- The initial state of a typed context. -/
theorem wp_init_iff {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr}
    {lt st gt : List IntType} {mem : Bool} {c : XCtx H}
    (hc : c.Ok lt st gt mem) {a : List Instr} {A : XState} (ha : xsexec mem (initX lt st gt) a = some A)
    (us : List Val) (rest : List Admin) (Q : Post H) :
    Wp m P host c.s c.f (c.code lt st gt us a rest) Q ↔ XOut m P host c mem A us rest Q :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_init_iff (H := H) (P := P) (host := host) (m := m) (lt := lt)
    (st := st) (gt := gt) (mem := mem) (c := c) (hc := hc) (a := a) (A := A) (ha := ha) (us := us)
    (rest := rest) (Q := Q)

/-- **The equivalence check is sound.** -/
theorem segEquivX_of_checkX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkX lt st gt mem a b = true) : SegEquivX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.segEquivX_of_checkX (lt := lt) (st := st) (gt := gt) (mem := mem)
    (a := a) (b := b) (h := h)

theorem firstFail_none_iff {ρ : Env} {B0 : ByteArray} :
    ∀ {G : List (Guard × XState)}, firstFail ρ B0 G = none ↔ ∀ g ∈ G, g.1.holds ρ B0 = true :=
  Silmaril.Proofs.Wasm.Auto.Equiv.firstFail_none_iff (ρ := ρ) (B0 := B0)

/-- **The refinement check is sound.** -/
theorem segRefinesX_of_refinesX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : refinesX lt st gt mem a b = true) : SegRefinesX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.segRefinesX_of_refinesX (lt := lt) (st := st) (gt := gt) (mem := mem)
    (a := a) (b := b) (h := h)

theorem wp_vals_iff' {H : Type} {P : Profile} {host : HostSemantics H} {m : Corr} {s : Store H}
    {F : Frame} {vs : List Val} {Q : Post H} :
    Wp m P host s F (vals vs) Q ↔ Q s F (.normal vs) :=
  Silmaril.Proofs.Wasm.Auto.Equiv.wp_vals_iff' (H := H) (P := P) (host := host) (m := m) (s := s)
    (F := F) (vs := vs) (Q := Q)

/-- **The result check is sound.** -/
theorem outEquivX_of_checkOutX {lt st gt : List IntType} {mem : Bool} {a b : List Instr}
    (h : checkOutX lt st gt mem a b = true) : OutEquivX lt st gt mem a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.outEquivX_of_checkOutX (lt := lt) (st := st) (gt := gt) (mem := mem)
    (a := a) (b := b) (h := h)

/-- **`SegEquivX` without globals and memory gives `CEquiv`**, so the congruence rules of
`Silmaril.Wasm.Auto.Equiv` (`block`, `if`, `br_if`, `loop`) apply to it. -/
theorem SegEquivX.cequiv {lt st : List IntType} {a b : List Instr}
    (h : SegEquivX lt st [] false a b) : Silmaril.Wasm.Auto.Equiv.CEquiv lt st a b :=
  Silmaril.Proofs.Wasm.Auto.Equiv.SegEquivX.cequiv (lt := lt) (st := st) (a := a) (b := b) (h := h)

end


/-! ## Results used by `Silmaril.Wasm.Auto2` -/

section
-- Lemmas of `Silmaril.Proofs.Wasm.Auto.Equiv` that the proofs of `Silmaril.Wasm.Auto2` use.

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

theorem xstep_globs {mem : Bool} {S S' : XState} {i : Instr} (h : xstep mem S i = some S') :
    S'.globs.length = S.globs.length :=
  Silmaril.Proofs.Wasm.Auto.Equiv.xstep_globs h

theorem firstFail_append_none {ρ : Env} {B0 : ByteArray} :
    ∀ {G : List (Guard × XState)} (G' : List (Guard × XState)), firstFail ρ B0 G = none →
      firstFail ρ B0 (G ++ G') = firstFail ρ B0 G' :=
  Silmaril.Proofs.Wasm.Auto.Equiv.firstFail_append_none

end

end Silmaril.Wasm.Auto.Equiv
