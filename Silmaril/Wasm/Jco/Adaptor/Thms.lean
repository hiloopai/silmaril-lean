module

public import Silmaril.Wasm.Jco.Adaptor.Defs
public import Silmaril.Wasm.Jco.Basic.Thms

/-!
# Adaptor modules: execution lemmas

* `exec_append`: running `a ++ b` runs `a`, then `b`;
* `exec_nil`, `exec_cons`: the defining equations;
* `step_localGet`, `step_i32Const`, `step_call`, `step_localSet`: the instructions on frames that
  do not trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)
open RM

variable (M : CoreInst)

@[simp] theorem exec_nil (f : Frame) : exec M [] f = pure f := rfl

theorem exec_cons (i : AInstr) (is : List AInstr) (f : Frame) :
    exec M (i :: is) f = (i.step M f >>= fun f' => exec M is f') := rfl

theorem exec_append (a b : List AInstr) (f : Frame) :
    exec M (a ++ b) f = (exec M a f >>= fun f' => exec M b f') := by
  induction a generalizing f with
  | nil => simp
  | cons i is ih => simp only [List.cons_append, exec_cons, ih, bind_assoc]

theorem step_localGet {ls : List Flat} {i : Nat} {v : Flat} (h : ls[i]? = some v)
    (st : List Flat) : (AInstr.localGet i).step M ⟨ls, st⟩ = pure ⟨ls, v :: st⟩ := by
  simp [AInstr.step, h]

theorem step_i32Const (c : BitVec 32) (f : Frame) :
    (AInstr.i32Const c).step M f = pure ⟨f.locals, Flat.i32 c :: f.stack⟩ := rfl

theorem step_localSet {ls : List Flat} {i : Nat} (h : i < ls.length) (v : Flat)
    (st : List Flat) : (AInstr.localSet i).step M ⟨ls, v :: st⟩ = pure ⟨ls.set i v, st⟩ := by
  simp [AInstr.step, h]

theorem step_call (g : String) {n : Nat} (f : Frame) (h : n ≤ f.stack.length) :
    (AInstr.call g n).step M f =
      (M.call g (f.stack.take n).reverse >>= fun rs =>
        pure ⟨f.locals, rs.reverse ++ f.stack.drop n⟩) := by
  simp [AInstr.step, h]

end Silmaril.Wasm.Jco
