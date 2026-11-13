module

public import Silmaril.Proofs.Wasi.Examples.Handles

/-!
# The stdout example: stream handles are used only while live, for every host

`hello_inv`: the invariant of `hello` against `stdoutHandles` (no assumption on the host): from
the answer of `get-stdout` to the drop, the stream handle is live (`Has`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Examples

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol HEv handleProto handleStep Role)

/-- An answer of another function than `get-stdout` allocates nothing. -/
theorem stdoutHEv_imp_ne {f : FnName} (hf : f ≠ getStdout) (a : List Val) (n : Option (List Val)) :
    stdoutHEv (.imp f a n) = .skip := by
  unfold stdoutHEv
  split <;> simp_all

/-- The answer of `get-stdout` is a handle, or `hello` gives up and allocates nothing. -/
theorem helloK1_cases (n : Option (List Val)) : (∃ hd, n = some [.u32 hd]) ∨
    (helloK1 n = .pure (some [errV none]) ∧ stdoutHEv (.imp getStdout [] n) = .skip) := by
  unfold helloK1
  split
  · exact .inl ⟨_, rfl⟩
  · refine .inr ⟨rfl, ?_⟩
    unfold stdoutHEv
    split <;> simp_all

theorem write_hev (hd : BitVec 32) : stdoutHEv (wev (X := stdoutWorld.exports)
    (.inl (.ask (writeOp hd)))) = .use hd :=
  ite_eq_left rfl

theorem drop_hev (hd : BitVec 32) : stdoutHEv (wev (X := stdoutWorld.exports)
    (.inl (.ask (dropOp hd)))) = .free hd := by
  show (if streamDrop = streamWrite then HEv.use hd else if streamDrop = streamDrop then .free hd
    else .skip) = .free hd
  rw [ite_eq_right (by decide), ite_eq_left rfl]

/-- The control state of `hello` and the handle state. -/
def HelloInv (c : CSt stdoutWorld.imports stdoutWorld.exports) (_ : Unit)
    (qG : Option (List (BitVec 32))) : Prop :=
  (c = .idle ∨ (∃ q, c = .run q helloProg) ∨ (∃ q, c = .wait q getOp helloK1) ∨
    (∃ q r, c = .run q (.pure r)) ∨ (∃ q hd, c = .wait q (dropOp hd) helloK3)) ∨
  (∃ hd, Has hd qG ∧ ((∃ q, c = .run q (.call (writeOp hd) (helloK2 hd))) ∨
    (∃ q, c = .wait q (writeOp hd) (helloK2 hd)) ∨ (∃ q, c = .run q (.call (dropOp hd) helloK3))))

/-- The conclusion of one step of `hello`. -/
abbrev HelloStep (o : Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports))
    (c' : CSt stdoutWorld.imports stdoutWorld.exports) (qG : Option (List (BitVec 32))) : Prop :=
  ∃ qG', stdoutHandles.step qG (wev o) = some qG' ∧ HelloInv c' () qG'

theorem hello_idle {o c' qG} (hc : CStep hello .idle o c') : HelloStep o c' qG := by
  obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
  exact ⟨qG, skip_step qG, .inl (.inr (.inl ⟨q, rfl⟩))⟩

theorem hello_start {q o c' qG} (hc : CStep hello (.run q helloProg) o c') : HelloStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := getOp) (k := helloK1) hc
  exact ⟨qG, skip_step qG, .inl (.inr (.inr (.inl ⟨q, rfl⟩)))⟩

theorem hello_got {q o c' qG} (hc : CStep hello (.wait q getOp helloK1) o c') :
    HelloStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  rcases helloK1_cases n with ⟨hd, rfl⟩ | ⟨hk, hs⟩
  · obtain ⟨q', hq', hhd, -⟩ := alloc_step qG hd
    have he : stdoutHEv (.imp getStdout [] (some [.u32 hd])) = .alloc hd := ite_eq_left rfl
    exact ⟨q', (stdoutHandles_step _ _).trans (he ▸ hq'), .inr ⟨hd, hhd, .inl ⟨q, rfl⟩⟩⟩
  · refine ⟨qG, (stdoutHandles_step _ _).trans (hs ▸ skip_step qG), ?_⟩
    exact .inl (.inr (.inr (.inr (.inl ⟨q, some [errV none], by rw [hk]⟩))))

theorem hello_write {q hd o c' qG} (hhd : Has hd qG)
    (hc : CStep hello (.run q (.call (writeOp hd) (helloK2 hd))) o c') : HelloStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨qG, (stdoutHandles_step _ _).trans ((write_hev hd) ▸ use_step hhd),
    .inr ⟨hd, hhd, .inr (.inl ⟨q, rfl⟩)⟩⟩

theorem hello_written {q hd o c' qG} (hhd : Has hd qG)
    (hc : CStep hello (.wait q (writeOp hd) (helloK2 hd)) o c') : HelloStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hs : stdoutHEv (.imp streamWrite [.u32 hd, bytesV hiBytes] n) = .skip :=
    stdoutHEv_imp_ne (by decide) _ _
  exact ⟨qG, (stdoutHandles_step _ _).trans (hs ▸ skip_step qG),
    .inr ⟨hd, hhd, .inr (.inr ⟨q, rfl⟩)⟩⟩

theorem hello_drop {q hd o c' qG} (hhd : Has hd qG)
    (hc : CStep hello (.run q (.call (dropOp hd) helloK3)) o c') : HelloStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  obtain ⟨q', hq'⟩ := free_step hhd
  exact ⟨q', (stdoutHandles_step _ _).trans ((drop_hev hd) ▸ hq'),
    .inl (.inr (.inr (.inr (.inr ⟨q, hd, rfl⟩))))⟩

theorem hello_dropped {q hd o c' qG} (hc : CStep hello (.wait q (dropOp hd) helloK3) o c') :
    HelloStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hs : stdoutHEv (.imp streamDrop [.u32 hd] n) = .skip := stdoutHEv_imp_ne (by decide) _ _
  exact ⟨qG, (stdoutHandles_step _ _).trans (hs ▸ skip_step qG),
    .inl (.inr (.inr (.inr (.inl ⟨q, _, rfl⟩))))⟩

theorem hello_ret {q r o c' qG} (hc : CStep hello (.run q (.pure r)) o c') : HelloStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.pure_inv
  exact ⟨qG, skip_step qG, .inl (.inl rfl)⟩

/-- **The invariant of `hello`.** -/
theorem hello_inv : Inv hello topP stdoutHandles HelloInv where
  init := .inl (.inl rfl)
  step := fun hc hJ _ => by
    rcases hJ with (rfl | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, r, rfl⟩ | ⟨q, hd, rfl⟩) |
      ⟨hd, hhd, ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩⟩
    · exact hello_idle hc
    · exact hello_start hc
    · exact hello_got hc
    · exact hello_ret hc
    · exact hello_dropped hc
    · exact hello_write hhd hc
    · exact hello_written hhd hc
    · exact hello_drop hhd hc

end Silmaril.Wasi.Examples
