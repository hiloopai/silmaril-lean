module

public import Silmaril.Wasm.Models.FXAsync.Defs

/-!
# Liveness-based save sets: the handler kernel with locals

The handler kernel `FXAsync.sstep` has no local variables, so every asyncify strategy saves a
frame's whole state (its code position and operands). Binaryen's Asyncify also has locals, and
saves at a call site only the locals that are **live** after it. This module extends the kernel
with locals and states that optimization, for any strategy that saves frames:

* `LIns`: the kernel's instructions and `get x`, `set x` (read and write local `x`);
* `LFrame`: a frame with locals `Nat → SV V` (all `dflt` at entry; arguments arrive on the
  operand stack as in the kernel and are moved into locals with `set`);
* `live c x`: local `x` is read by the straight-line code `c` before it is written (backward
  liveness; the kernel has no branches inside a body, `cond` is a call);
* `Save`: what a frame keeps of its locals when it is **saved**: as a caller waiting on a call,
  as a resumer waiting on a `resume`, and as the suspender captured in a continuation. `keep`
  keeps everything (the source: what a plain kernel with locals does); `liveSave` keeps only
  the live locals of the code after the save point and resets the others to `dflt` (the
  optimized save set: a record needs to store only `saveSet c n`);
* `lstep P sv test`: the kernel with locals, saving frames with `sv`.

The results (`Thms`) show that any save function that keeps the live locals (`KeepsLive`), in
particular `liveSave`, gives the same behaviours as `keep`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Live

open Silmaril.Wasm.Models.FXAsync

/-- Kernel instructions with locals. -/
inductive LIns (V : Type) where
  | push (v : V)
  | prim (n : Nat) (op : List V → List V)
  | drop
  | get (x : Nat)
  | set (x : Nat)
  | call (f : Nat)
  | cond (f g : Nat)
  | contNew (f : Nat)
  | resume (n : Nat) (hs : List Clause)
  | suspend (t n : Nat)

/-- Locals of a frame. -/
abbrev Locals (V : Type) := Nat → SV V

/-- A frame with locals. -/
structure LFrame (V : Type) where
  code : List (LIns V)
  ops : List (SV V)
  locals : Locals V
  wait : Option (List Clause)

/-- A configuration: continuation store and stack (top first). -/
structure LCfg (V : Type) where
  conts : List (Option (List (LFrame V)))
  stack : List (LFrame V)

variable {V : Type}

/-- The value of a local before it is written. -/
def dflt : SV V := .cont 0

/-- Fresh locals. -/
def fresh : Locals V := fun _ => dflt

/-- Write local `x`. -/
def upd (ls : Locals V) (x : Nat) (v : SV V) : Locals V := fun y => if y = x then v else ls y

/-- **Liveness**: `x` is read by `c` before it is written. -/
def live : List (LIns V) → Nat → Bool
  | [], _ => false
  | .get x :: c, y => x == y || live c y
  | .set x :: c, y => x != y && live c y
  | _ :: c, y => live c y

/-- What a saved frame keeps of its locals, given the code it resumes with. -/
abbrev Save (V : Type) := List (LIns V) → Locals V → Locals V

/-- Keep every local. -/
def keep : Save V := fun _ ls => ls

/-- **Keep only the live locals** of the code after the save point. -/
def liveSave : Save V := fun c ls y => if live c y then ls y else dflt

/-- The locals below `n` that a record saved before `c` stores. -/
def saveSet (c : List (LIns V)) (n : Nat) : List Nat := (List.range n).filter (live c)

/-- A save function keeps the live locals. -/
def KeepsLive (sv : Save V) : Prop := ∀ c ls y, live c y = true → sv c ls y = ls y

/-- The innermost frame waiting on a `resume` with a clause for `t`. -/
def lsplit (t : Nat) : List (LFrame V) → Option (List (LFrame V) × Nat × LFrame V × List (LFrame V))
  | [] => none
  | b :: rest =>
    match b.wait.bind (lookup t) with
    | some h => some ([], h, b, rest)
    | none => (lsplit t rest).map fun x => (b :: x.1, x.2)

/-- Call `f` from the top frame `fr`, which is saved with code `c`. -/
def lcall (P : Prog (LIns V)) (sv : Save V) (K : List (Option (List (LFrame V)))) (f : Nat)
    (fr : LFrame V) (ops : List (SV V)) (c : List (LIns V)) (rest : List (LFrame V)) :
    Res (LCfg V) V :=
  match P f with
  | none => .stop .trap
  | some (np, body) =>
    match popN np ops with
    | none => .stop .trap
    | some (args, o) =>
      .next ⟨K, ⟨body, args, fresh, none⟩ ::
        { fr with code := c, ops := o, locals := sv c fr.locals, wait := none } :: rest⟩

/-- Execute instruction `i` of the top frame `fr` (code `i :: c`). -/
def lexec (P : Prog (LIns V)) (sv : Save V) (test : V → Bool)
    (K : List (Option (List (LFrame V)))) (fr : LFrame V) (i : LIns V) (c : List (LIns V))
    (rest : List (LFrame V)) : Res (LCfg V) V :=
  match i with
  | .push v => .next ⟨K, { fr with code := c, ops := .val v :: fr.ops } :: rest⟩
  | .prim n op =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (a, o) =>
      match allVals a with
      | none => .stop .trap
      | some vs => .next ⟨K, { fr with code := c, ops := (op vs).map .val ++ o } :: rest⟩
  | .drop =>
    match fr.ops with
    | [] => .stop .trap
    | _ :: o => .next ⟨K, { fr with code := c, ops := o } :: rest⟩
  | .get x => .next ⟨K, { fr with code := c, ops := fr.locals x :: fr.ops } :: rest⟩
  | .set x =>
    match fr.ops with
    | [] => .stop .trap
    | v :: o => .next ⟨K, { fr with code := c, ops := o, locals := upd fr.locals x v } :: rest⟩
  | .call f => lcall P sv K f fr fr.ops c rest
  | .cond f g =>
    match fr.ops with
    | .val v :: o => lcall P sv K (if test v then f else g) fr o c rest
    | _ => .stop .trap
  | .contNew f =>
    match P f with
    | none => .stop .trap
    | some (_, body) =>
      .next ⟨K ++ [some [⟨body, [], fresh, none⟩]],
        { fr with code := c, ops := .cont K.length :: fr.ops } :: rest⟩
  | .resume n hs =>
    match fr.ops with
    | .cont k :: o =>
      match popN n o with
      | none => .stop .trap
      | some (args, o') =>
        match K[k]? with
        | some (some (top :: seg)) =>
          .next ⟨K.set k none, { top with ops := args ++ top.ops } :: seg ++
            { fr with code := c, ops := o', locals := sv c fr.locals, wait := some hs } :: rest⟩
        | _ => .stop .trap
    | _ => .stop .trap
  | .suspend t n =>
    match popN n fr.ops with
    | none => .stop .trap
    | some (p, o) =>
      match lsplit t rest with
      | none => .stop .trap
      | some (m, h, r, rs) =>
        match P h with
        | none => .stop .trap
        | some (_, body) =>
          .next ⟨K ++ [some ({ fr with code := c, ops := o, locals := sv c fr.locals } :: m)],
            ⟨body, .cont K.length :: p, fresh, none⟩ :: { r with wait := none } :: rs⟩

/-- **The kernel with locals**, saving frames with `sv`. -/
def lstep (P : Prog (LIns V)) (sv : Save V) (test : V → Bool) (x : LCfg V) : Res (LCfg V) V :=
  match x.stack with
  | [] => .stop .trap
  | fr :: rest =>
    match fr.code with
    | [] =>
      match rest with
      | [] => .stop (.done fr.ops)
      | b :: rest' => .next ⟨x.conts, { b with ops := fr.ops ++ b.ops } :: rest'⟩
    | i :: c => lexec P sv test x.conts fr i c rest

/-- The configuration that calls `f` with arguments `args`. -/
def lInit (f : Nat) (args : List (SV V)) : LCfg V := ⟨[], [⟨[.call f], args, fresh, none⟩]⟩

end Silmaril.Wasm.FX.Asyncify.Live
