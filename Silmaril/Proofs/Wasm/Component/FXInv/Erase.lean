module

public import Silmaril.Wasm.Component.FXInv.Defs
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# Inversion of `StepFX` at host calls: the erasure lemmas

* `eraseL_*`: the Core erasure commutes with append and is the identity on Core code;
* `decompose?_vals_append_some`: a host-call redex survives a value prefix and any suffix, with
  the same callee, host code and arguments;
* `decompose?_erase_plug`: FX code at a host call erases to Core code at the same host call;
* `NoHostRedex.*`: `NoHostRedex` is closed under value prefixes and suffixes and under FX
  contexts, and holds below labels, frames and handler frames around host-free code.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Models.FX (AdminFX cvals cthrowing)
open Silmaril.Wasm.Component.FXEngine (FXCode)
open Silmaril.Wasm.Component.FXInv

variable {H : Type}

/-! ## The erasure -/

theorem eraseL_eq (l : List AdminFX) : eraseL l = l.map eraseA := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [eraseL, ih]

@[simp] theorem eraseL_nil : eraseL [] = [] := rfl

@[simp] theorem eraseL_cons (a : AdminFX) (as : List AdminFX) :
    eraseL (a :: as) = eraseA a :: eraseL as := rfl

@[simp] theorem eraseL_append (l₁ l₂ : List AdminFX) :
    eraseL (l₁ ++ l₂) = eraseL l₁ ++ eraseL l₂ := by
  simp [eraseL_eq]

@[simp] theorem eraseL_map_core (cs : List Admin) : eraseL (cs.map .core) = cs := by
  induction cs with
  | nil => rfl
  | cons a as ih => simp [ih, eraseA]

@[simp] theorem eraseL_cvals (vs : List Execution.Core.Val) : eraseL (cvals vs) = vals vs :=
  eraseL_map_core _

@[simp] theorem eraseL_cthrowing (a : Nat) : eraseL (cthrowing a) = throwing a :=
  eraseL_map_core _

/-! ## Host-call redexes under a value prefix -/

theorem topRedex_inv {s : Store (FXCode H)} {ws : List Execution.Core.Val} {r : List Admin}
    {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H} {args : List Execution.Core.Val}
    (ht : topRedex s ws r = some (Ec, a, h, args)) :
    ∃ ys n, ws = ys ++ [.ref (.func a)] ∧ hostArity? s a = some (h, n) ∧ n ≤ ys.length ∧
      args = ys.drop (ys.length - n) := by
  unfold topRedex at ht
  split at ht
  · rename_i a' hl
    split at ht
    · rename_i h' n hh
      dsimp only at ht
      split at ht
      · rename_i hn
        obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
        simp only [Option.some.injEq, Prod.mk.injEq, List.dropLast_concat] at ht hn
        obtain ⟨-, rfl, rfl, rfl⟩ := ht
        exact ⟨ys, n, rfl, hh, hn, rfl⟩
      · cases ht
    · cases ht
  · cases ht

theorem topRedex_of {s : Store (FXCode H)} {ys : List Execution.Core.Val} {r : List Admin}
    {a n : Nat} {h : FXCode H} (hh : hostArity? s a = some (h, n)) (hn : n ≤ ys.length) :
    topRedex s (ys ++ [.ref (.func a)]) r =
      some (.top (ys.take (ys.length - n)) r, a, h, ys.drop (ys.length - n)) := by
  unfold topRedex
  simp only [List.getLast?_concat, hh, List.dropLast_concat]
  exact ite_eq_left hn

theorem topRedex_append {s : Store (FXCode H)} {ws : List Execution.Core.Val} {r : List Admin}
    {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H} {args : List Execution.Core.Val}
    (ht : topRedex s ws r = some (Ec, a, h, args)) (pre : List Execution.Core.Val)
    (r' : List Admin) : ∃ Ec', topRedex s (pre ++ ws) r' = some (Ec', a, h, args) := by
  obtain ⟨ys, n, hws, hh, hn, hargs⟩ := topRedex_inv ht
  have hpre : pre ++ ws = (pre ++ ys) ++ [.ref (.func a)] := by simp [hws]
  have hlen : n ≤ (pre ++ ys).length := by simp only [List.length_append]; omega
  have hdrop : (pre ++ ys).drop ((pre ++ ys).length - n) = args := by
    rw [List.length_append, show pre.length + ys.length - n = pre.length + (ys.length - n) by omega,
      List.drop_append, hargs]
    simp
  exact ⟨_, by rw [hpre, topRedex_of hh hlen, hdrop]⟩

/-- A `map` over a redex that keeps the callee, host code and arguments. -/
theorem map_redex_some {o : Option (SingleThreaded.Ctx × Nat × FXCode H × List Execution.Core.Val)}
    {g g' : SingleThreaded.Ctx → SingleThreaded.Ctx} {Ec : SingleThreaded.Ctx} {a : Nat}
    {h : FXCode H} {args : List Execution.Core.Val}
    (hd : o.map (fun (E, a, h, args) => (g E, a, h, args)) = some (Ec, a, h, args)) :
    ∃ Ec', o.map (fun (E, a, h, args) => (g' E, a, h, args)) = some (Ec', a, h, args) := by
  obtain ⟨⟨E', a', h', args'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp hd
  simp only [Prod.mk.injEq] at h2
  obtain ⟨-, rfl, rfl, rfl⟩ := h2
  exact ⟨g' E', by rw [h1]; rfl⟩

theorem isCallRef_false {d : Admin} (hc : ¬ d.IsCallRef) : d.isCallRef = false := by
  cases e : d.isCallRef
  · rfl
  · exact absurd (Admin.IsCallRef_of_isCallRef e) hc

/-- One layer of a host-call redex survives a longer value prefix and suffix. -/
theorem decompHead_append {s : Store (FXCode H)} {ws : List Execution.Core.Val} {d : Admin}
    {r : List Admin} {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H}
    {args : List Execution.Core.Val} (hd : decompHead s ws d r = some (Ec, a, h, args))
    (pre : List Execution.Core.Val) (rest : List Admin) :
    ∃ Ec', decompHead s (pre ++ ws) d (r ++ rest) = some (Ec', a, h, args) := by
  by_cases hc : d.IsCallRef
  · have ht : topRedex s ws r = some (Ec, a, h, args) := (decompHead_of_IsCallRef hc).symm.trans hd
    simpa only [decompHead_of_IsCallRef hc] using topRedex_append ht pre (r ++ rest)
  cases d with
  | label n cont body =>
      exact map_redex_some (g := fun E => .label ws n cont E r)
        (g' := fun E => .label (pre ++ ws) n cont E (r ++ rest)) hd
  | handler n cs body =>
      exact map_redex_some (g := fun E => .handler ws n cs E r)
        (g' := fun E => .handler (pre ++ ws) n cs E (r ++ rest)) hd
  | frame n f body =>
      exact map_redex_some (g := fun E => .frame ws n f E r)
        (g' := fun E => .frame (pre ++ ws) n f E (r ++ rest)) hd
  | plain i => exact absurd hd (by rw [decompHead_plain (isCallRef_false hc)]; simp)
  | ref _ => exact absurd hd (by simp [decompHead, Admin.isCallRef])
  | callRefType _ => exact absurd trivial hc
  | returnCallRefType _ => exact absurd hd (by simp [decompHead, Admin.isCallRef])
  | trap => exact absurd hd (by simp [decompHead_trap])

theorem decompose?_vals_append_some {s : Store (FXCode H)} {cs : List Admin}
    {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H} {args : List Execution.Core.Val}
    (hd : decompose? s cs = some (Ec, a, h, args)) (pre : List Execution.Core.Val)
    (rest : List Admin) : ∃ Ec', decompose? s (vals pre ++ cs ++ rest) = some (Ec', a, h, args) := by
  rcases hsp : splitVals cs with ⟨ws, _ | ⟨d, r⟩⟩
  · exact absurd hd (by rw [decompose?_of_split_nil hsp]; simp)
  have hd' : decompHead s ws d r = some (Ec, a, h, args) := by
    rwa [decompose?_of_split hsp] at hd
  rw [decompose?_of_split (splitVals_append_of_cons hsp pre rest)]
  exact decompHead_append hd' pre rest

/-- A host-call redex of the body of a label, frame or handler frame is one of the wrapper. -/
theorem decompose?_single_some {s : Store (FXCode H)} {d : Admin} {body : List Admin}
    {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H} {args : List Execution.Core.Val}
    (hd : decompose? s body = some (Ec, a, h, args))
    (hw : (∃ n cont, d = .label n cont body) ∨ (∃ n cs, d = .handler n cs body) ∨
      ∃ n f, d = .frame n f body) :
    ∃ Ec', decompose? s [d] = some (Ec', a, h, args) := by
  rcases hw with ⟨n, cont, rfl⟩ | ⟨n, cs, rfl⟩ | ⟨n, f, rfl⟩
  · rw [decompose?_of_split (splitVals_label_cons n cont body []), decompHead_label, hd]
    exact ⟨_, rfl⟩
  · rw [decompose?_of_split (splitVals_handler_cons n cs body []), decompHead_handler, hd]
    exact ⟨_, rfl⟩
  · rw [decompose?_of_split (splitVals_frame_cons n f body []), decompHead_frame, hd]
    exact ⟨_, rfl⟩

/-- **FX code at a host call erases to Core code at the same host call.** -/
theorem decompose?_erase_plug {s : Store (FXCode H)} {cs : List Admin}
    {Ec : SingleThreaded.Ctx} {a : Nat} {h : FXCode H} {args : List Execution.Core.Val}
    (hd : decompose? s cs = some (Ec, a, h, args)) (E : Silmaril.Wasm.Models.FX.Ctx) :
    ∃ Ec', decompose? s (eraseL (E.plug (cs.map .core))) = some (Ec', a, h, args) := by
  induction E with
  | hole => exact ⟨Ec, by simpa [Silmaril.Wasm.Models.FX.Ctx.plug] using hd⟩
  | seq vs E rest ih =>
    obtain ⟨Ec', h'⟩ := ih
    simpa [Silmaril.Wasm.Models.FX.Ctx.plug, List.append_assoc] using
      decompose?_vals_append_some h' vs (eraseL rest)
  | label n k E ih =>
    obtain ⟨Ec', h'⟩ := ih
    exact decompose?_single_some h' (Or.inl ⟨n, [], rfl⟩)
  | frame n f E ih =>
    obtain ⟨Ec', h'⟩ := ih
    exact decompose?_single_some h' (Or.inr (Or.inr ⟨n, f, rfl⟩))
  | handler hs E ih =>
    obtain ⟨Ec', h'⟩ := ih
    exact decompose?_single_some h' (Or.inr (Or.inl ⟨0, [], rfl⟩))

/-! ## `NoHostRedex` -/

theorem hostFree_of_none {s : Store (FXCode H)} {l : List Admin} (h : decompose? s l = none) :
    HostFree s l := fun _ _ _ _ e => by rw [h] at e; cases e

theorem NoHostRedex.hostFree {s : Store (FXCode H)} {l : List Admin} (h : NoHostRedex s l) :
    HostFree s l := by
  simpa using h [] []

theorem noHostRedex_of_noRedex {s : Store (FXCode H)} {l : List Admin} (h : NoRedex s l) :
    NoHostRedex s l := fun pre rest => hostFree_of_none (h pre rest)

theorem NoHostRedex.seq {s : Store (FXCode H)} {l : List Admin} (h : NoHostRedex s l)
    (vs : List Execution.Core.Val) (r : List Admin) : NoHostRedex s (vals vs ++ l ++ r) := by
  intro pre rest
  simpa [List.append_assoc] using h (pre ++ vs) (r ++ rest)

/-- Below a label, frame or handler frame, host-free code has no host-call redex. -/
theorem noHostRedex_single {s : Store (FXCode H)} {d : Admin} {body : List Admin}
    (hb : HostFree s body)
    (hw : (∃ n cont, d = .label n cont body) ∨ (∃ n cs, d = .handler n cs body) ∨
      ∃ n f, d = .frame n f body) : NoHostRedex s [d] := by
  intro pre rest Ec a h args e
  have hv : d.val? = none := by
    rcases hw with ⟨n, cont, rfl⟩ | ⟨n, cs, rfl⟩ | ⟨n, f, rfl⟩ <;> rfl
  rw [show vals pre ++ [d] ++ rest = vals pre ++ d :: rest by simp,
    decompose?_of_split (splitVals_vals_cons hv rest)] at e
  rcases hw with ⟨n, cont, rfl⟩ | ⟨n, cs, rfl⟩ | ⟨n, f, rfl⟩
  all_goals
    first
    | rw [decompHead_label] at e
    | rw [decompHead_handler] at e
    | rw [decompHead_frame] at e
    obtain ⟨⟨E', a', h', args'⟩, h1, h2⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at h2
    obtain ⟨-, rfl, rfl, rfl⟩ := h2
    exact hb _ _ _ _ h1

theorem hostFree_vals {s : Store (FXCode H)} (vs : List Execution.Core.Val) :
    HostFree s (vals vs) := hostFree_of_none decompose?_vals_nil

/-- `NoHostRedex` is closed under FX evaluation contexts. -/
theorem NoHostRedex.plug {s : Store (FXCode H)} {Y : List AdminFX}
    (h : NoHostRedex s (eraseL Y)) (E : Silmaril.Wasm.Models.FX.Ctx) :
    NoHostRedex s (eraseL (E.plug Y)) := by
  induction E with
  | hole => exact h
  | seq vs E rest ih => simpa [Silmaril.Wasm.Models.FX.Ctx.plug] using NoHostRedex.seq ih vs (eraseL rest)
  | label n k E ih => exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inl ⟨n, [], rfl⟩)
  | frame n f E ih => exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inr (Or.inr ⟨n, f, rfl⟩))
  | handler hs E ih => exact noHostRedex_single (NoHostRedex.hostFree ih) (Or.inr (Or.inl ⟨0, [], rfl⟩))

end Silmaril.Proofs.Wasm.Component.FXInv
