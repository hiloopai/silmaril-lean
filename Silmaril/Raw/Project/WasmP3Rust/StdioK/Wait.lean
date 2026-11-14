module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Rw

/-!
# `cat` and `echo` under `DenX.den`: the answers to `waitable-set.wait`

The wait discipline makes a `STREAM_READ` event the completion of the blocked read (with its
data, which `DenX.den` stores into the read buffer) and a `STREAM_WRITE` event the completion
of the blocked write; other events re-enter the callback, which returns `WAIT` again (a
`FUTURE_READ` event may store a result byte).
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

theorem cWait_ne₁ : cWait ≠ cStreamNew := by decide
theorem cWait_ne₂ : cWait ≠ stdoutWrite3 := by decide
theorem cWait_ne₃ : cWait ≠ cStreamWrite := by decide
theorem cWait_ne₄ : cWait ≠ cStreamRead := by decide
theorem cWait_ne₅ : cWait ≠ stdinRead3 := by decide
theorem cWait_ne₆ : cWait ≠ getArgs3 := by decide

/-! ## The observations on wait answers -/

theorem os_wait_fst (q : OsSt) (a : List Val) (n : Option (List Val)) :
    (osStep3 0 q (.imp cWait a n)).1 = q := by
  unfold osStep3
  dsimp only
  simp only [cWait_ne₁, cWait_ne₂, cWait_ne₃, ite_false, ite_true]
  split <;> (repeat' split) <;> rfl

theorem os_wait_quiet (q : OsSt) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv, n = some [cv, iv, pv] → natOf cv ≠ some 3 ∨ natOf iv = none ∨
      natOf pv = none) :
    osStep3 0 q (.imp cWait a n) = (q, []) := by
  unfold osStep3
  dsimp only
  simp only [cWait_ne₁, cWait_ne₂, cWait_ne₃, ite_false, ite_true]
  split
  · rename_i cv iv pv
    split
    · rename_i hcv hiv hpv
      rcases h cv iv pv rfl with h3 | h3 | h3
      · exact absurd hcv h3
      · rw [h3] at hiv; cases hiv
      · rw [h3] at hpv; cases hpv
    · rfl
  · rfl

theorem inStep_wait_quiet (rs : List Nat) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv it, n = some [cv, iv, pv, it] → natOf cv ≠ some evStreamRead ∨
      natOf iv = none ∨ natOf pv = none) :
    inStep rs (.imp cWait a n) = (rs, []) := by
  unfold inStep
  simp only [cWait_ne₅, cWait_ne₄, ite_false, ite_true]
  split
  · rename_i cv iv pv it
    split
    · rename_i c i k hcv hiv hpv
      rcases h cv iv pv it rfl with h2 | h2 | h2
      · have : c ≠ evStreamRead := fun e => h2 (e ▸ hcv)
        simp [this]
      · rw [h2] at hiv; cases hiv
      · rw [h2] at hpv; cases hpv
    · rfl
  · rfl

theorem waitX_quiet (q : List Nat × List Nat) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv rest, n = some (cv :: iv :: pv :: rest) →
      natOf cv ≠ some streamWriteCode ∧ natOf cv ≠ some evStreamRead) :
    waitStepX q (.imp cWait a n) = some q := by
  unfold waitStepX
  simp only [cWait_ne₃, cWait_ne₄, ite_false, ite_true]
  split
  · rename_i cv iv pv rest
    obtain ⟨h3, h2⟩ := h cv iv pv rest rfl
    simp only [h3, h2, ite_false]
  · rfl

/-- An answer that no observation reads. -/
theorem obsStep_wait_quiet (o : Obs) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv rest, n = some (cv :: iv :: pv :: rest) →
      natOf cv ≠ some streamWriteCode ∧ natOf cv ≠ some evStreamRead) :
    obsStep o (.imp cWait a n) = o := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  have h1 := os_wait_quiet os a n fun cv iv pv e => .inl (h cv iv pv [] e).1
  have h2 := inStep_wait_quiet rs a n fun cv iv pv it e => .inl (h cv iv pv [it] e).2
  simp only [obsStep, h1, h2, waitX_quiet _ a n h, wbytes, List.filterMap_nil, List.append_nil,
    okEv, Bool.or_false, argsStep_other cWait_ne₆]
  cases wp <;> rfl

/-- When the event is not one `DenX.den` reads (`evOf … = none`), no observation but the
wait discipline changes. -/
theorem obsStep_wait_evNone (o : Obs) (a : List Val) {n : Option (List Val)} (hn : evOf n = none) :
    (obsStep o (.imp cWait a n)).out = o.out ∧ (obsStep o (.imp cWait a n)).inp = o.inp ∧
      (obsStep o (.imp cWait a n)).args = o.args := by
  have h1 := os_wait_quiet o.os a n fun cv iv pv e => by
    subst e
    simp only [evOf] at hn
    split at hn
    · simp at hn
    · rename_i h; by_cases hc : natOf cv = some 3
      · right
        cases hi : natOf iv <;> cases hp : natOf pv <;> simp_all
      · exact .inl hc
  have h2 := inStep_wait_quiet o.rs a n fun cv iv pv it e => by
    subst e
    simp only [evOf] at hn
    split at hn
    · simp at hn
    · rename_i h
      by_cases hc : natOf cv = some evStreamRead
      · right
        cases hi : natOf iv <;> cases hp : natOf pv <;> simp_all
      · exact .inl hc
  refine ⟨?_, ?_, ?_⟩
  · simp only [obsStep, h1, wbytes, List.filterMap_nil, List.append_nil]
  · simp only [obsStep, h2, List.append_nil]
  · simp only [obsStep, argsStep_other cWait_ne₆]

theorem prefOk_congr {o o' : Obs} (hout : o'.out = o.out) (hinp : o'.inp = o.inp)
    (hargs : o'.args = o.args) (h : PrefOk P o) : PrefOk P o' := by
  have ht : tgt P o' = tgt P o := by simp only [tgt, hinp, hargs]
  unfold PrefOk at h ⊢
  rw [ht, hout]; exact h

/-- A `STREAM_WRITE` event not for a blocked write, or not of three values, is refused. -/
theorem obsStep_wait_refused3 {o : Obs} {q : List Nat × List Nat} (a : List Val)
    {cv iv pv : Val} {rest : List Val} (hwp : o.wp = some q) (hc : natOf cv = some 3)
    (hi : ∀ i, natOf iv = some i → rest = [] → i ∉ q.1) :
    (obsStep o (.imp cWait a (some (cv :: iv :: pv :: rest)))).wp = none := by
  simp only [obsStep, hwp, Option.bind_some, waitStepX, cWait_ne₃, cWait_ne₄, ite_false, ite_true,
    hc, streamWriteCode]
  cases h : natOf iv with
  | none => rfl
  | some i =>
    rcases rest with _ | ⟨x, rest⟩
    · simp only [hi i h rfl, ite_false]
    · rfl

/-- A `STREAM_READ` event not for a blocked read, or without its data, is refused. -/
theorem obsStep_wait_refused2 {o : Obs} {q : List Nat × List Nat} (a : List Val)
    {cv iv pv : Val} {rest : List Val} (hwp : o.wp = some q) (hc : natOf cv = some evStreamRead)
    (hi : ∀ i x, natOf iv = some i → rest = [x] → i ∉ q.2) :
    (obsStep o (.imp cWait a (some (cv :: iv :: pv :: rest)))).wp = none := by
  simp only [obsStep, hwp, Option.bind_some, waitStepX, cWait_ne₃, cWait_ne₄, ite_false, ite_true,
    hc, streamWriteCode, evStreamRead, show (some 2 : Option Nat) ≠ some 3 by decide]
  cases h : natOf iv with
  | none => rfl
  | some i =>
    rcases rest with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · rfl
    · simp only [hi i x h rfl, ite_false]
    · rfl

/-- The bytes a copy result reports as written, of the pending bytes `bs`. -/
def wout (x : Option (Option (CopyResult × Nat))) (bs : List (BitVec 8)) : List (BitVec 8) :=
  match x with
  | some (some (.completed, k)) => bs.take k
  | _ => []

/-- The `STREAM_WRITE` event of the blocked write. -/
theorem obsStep_wait_write {o : Obs} {w : Nat} {bs : List (BitVec 8)} (a : List Val)
    {cv iv pv : Val} (hwp : o.wp = some ([w], [])) (hc : natOf cv = some 3)
    (hi : natOf iv = some w) (hpend : o.os.pend.find? (·.1 = w) = some (w, bs))
    (hout : w ∈ o.os.outW) :
    obsStep o (.imp cWait a (some [cv, iv, pv])) =
      { o with out := o.out ++ wout ((natOf pv).bind copyOf) bs, wp := some ([], []) } := by
  have hos : osStep3 0 o.os (.imp cWait a (some [cv, iv, pv])) =
      (o.os, (wout ((natOf pv).bind copyOf) bs).map (.writeEv 0)) := by
    unfold osStep3
    dsimp only
    simp only [cWait_ne₁, cWait_ne₂, cWait_ne₃, ite_false, ite_true, hc, hi, Option.bind_eq_bind]
    generalize (natOf pv).bind copyOf = x
    rcases x with _ | _ | ⟨_ | _ | _, k⟩ <;> simp [hpend, hout, wout]
  have hin : inStep o.rs (.imp cWait a (some [cv, iv, pv])) = (o.rs, []) :=
    inStep_wait_quiet _ _ _ fun _ _ _ _ e => by cases e
  simp only [obsStep, hos, hin, wbytes_map, okEv, Bool.or_false, hwp, Option.bind_some, waitStepX,
    cWait_ne₃, ite_false, ite_true, hc, hi, streamWriteCode, List.mem_singleton,
    List.erase_cons_head, List.append_nil, argsStep_other cWait_ne₆]
  simp only [cWait_ne₄, ite_false]

/-- The `STREAM_READ` event of the blocked read, with its data. -/
theorem obsStep_wait_read {o : Obs} {r q : Nat} (a : List Val) {cv iv pv it : Val}
    (hwp : o.wp = some ([], [r])) (hrs : o.rs = [r]) (hc : natOf cv = some evStreamRead)
    (hi : natOf iv = some r) (hq : natOf pv = some q) :
    obsStep o (.imp cWait a (some [cv, iv, pv, it])) =
      { o with inp := o.inp ++ ((copyCount q).map fun k => (bytesOf it).take k).getD [],
               wp := some ([], []) } := by
  have hos : osStep3 0 o.os (.imp cWait a (some [cv, iv, pv, it])) = (o.os, []) :=
    os_wait_quiet _ _ _ fun _ _ _ e => by cases e
  have hin : inStep o.rs (.imp cWait a (some [cv, iv, pv, it])) =
      (o.rs, ((copyCount q).map fun k => (bytesOf it).take k).getD []) := by
    rw [hrs]
    rcases hcc : copyCount q with _ | k
    all_goals
      unfold inStep
      simp only [cWait_ne₅, cWait_ne₄, ite_false, ite_true, hc, hi, hq, Option.bind_eq_bind,
        Option.bind_some, hcc, List.mem_singleton, and_self, Option.map_none, Option.getD_none,
        Option.map_some, Option.getD_some]
  simp only [obsStep, hos, hin, wbytes, List.filterMap_nil, List.append_nil, okEv, Bool.or_false,
    hwp, Option.bind_some, waitStepX, cWait_ne₃, cWait_ne₄, ite_false, ite_true, hc, hi,
    streamWriteCode, evStreamRead, show (some 2 : Option Nat) ≠ some 3 by decide,
    List.mem_singleton, List.erase_cons_head, argsStep_other cWait_ne₆]

/-! ## The driver -/

theorem reenter_eq {d : DConf (stdioK P)} (ev : List Nat) (hwt : waiting d.core.pc = true) :
    reenter P.cb d ev = { d with core := onEvent P d.core ev, mode := .run } := by
  have hni : d.core.pc ≠ .init := fun e => by rw [e] at hwt; cases hwt
  simp only [reenter, stdioK, hni, false_and, and_false, ite_false, true_and, hwt, ite_true]

theorem evOf3 {cv iv pv : Val} {c i q : Nat} (hc : natOf cv = some c) (hi : natOf iv = some i)
    (hq : natOf pv = some q) : evOf (some [cv, iv, pv]) = some (c, i, q, none) := by
  simp only [evOf, hc, hi, hq]

theorem evOf4 {cv iv pv v : Val} {c i q : Nat} (hc : natOf cv = some c) (hi : natOf iv = some i)
    (hq : natOf pv = some q) : evOf (some [cv, iv, pv, v]) = some (c, i, q, some v) := by
  simp only [evOf, hc, hi, hq]

theorem afterWait_none {d : DConf (stdioK P)} {n : Option (List Val)} (h : evOf n = none) :
    afterWait P.cb d n = d.trapped := by
  simp only [afterWait, h]

theorem afterWait_some {d d' : DConf (stdioK P)} {n : Option (List Val)} {c i q : Nat}
    {v : Option Val} (h : evOf n = some (c, i, q, v)) (hd : deliver d c i v = some d') :
    afterWait P.cb d n = reenter P.cb d' [c, i, q] := by
  simp only [afterWait, h, hd]

theorem deliver_nofind {d : DConf (stdioK P)} {c i : Nat} {v : Option Val}
    (h : d.pend.find? (fun e => e.1 = c ∧ e.2.1 = i) = none) : deliver d c i v = some d := by
  unfold deliver
  split
  · simp only [h]
  · rfl

theorem deliver_read {d : DConf (stdioK P)} {r : Nat} (hpend : d.pend = [(evStreamRead, r, 0)])
    (v : Val) : deliver d evStreamRead r (some v) =
      some { d with pend := [], core := store d.core 0 (bytesOf v) } := by
  simp [deliver, hpend, DConf.store, evStreamRead]

/-- Delivering into the future buffer changes the result byte only. -/
theorem deliver_fut {d d' : DConf (stdioK P)} {c i : Nat} {v : Option Val} (hpf : PendF d.pend)
    (h : deliver d c i v = some d') :
    d'.mode = d.mode ∧ d'.result = d.result ∧ PendF d'.pend ∧ d'.core.pc = d.core.pc ∧
      d'.core.off = d.core.off ∧ d'.core.chunk = d.core.chunk ∧ d'.core.w = d.core.w ∧
      d'.core.rin = d.core.rin ∧ d'.core.s = d.core.s ∧ d'.core.f = d.core.f ∧
      d'.core.fin = d.core.fin := by
  unfold deliver at h
  split at h
  · split at h
    · rename_i x p hx
      have hmem := List.mem_of_find?_eq_some hx
      have hpp : p = futA := (hpf _ hmem).2
      subst hpp
      have hpf' : PendF (d.pend.filter (fun e => ¬ (e.1 = c ∧ e.2.1 = i))) :=
        fun e he => hpf e (List.mem_of_mem_filter he)
      split at h
      · simp only [DConf.store, stdioK, Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨rfl, rfl, hpf', ?_⟩
        split <;> simp [store, futA, retA]
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, hpf', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, hpf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, hpf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
