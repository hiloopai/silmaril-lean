module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Run

/-!
# `hello` under `den`: answers keep the invariant

One lemma per program point of `helloK` that calls the world: whatever the host answers, the
next configuration satisfies `DInv` for the observations extended by the answer, provided the
wait discipline accepts it.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-! ## Building the invariant -/

theorem dinv_trapped {o : Obs} {d : DConf helloK} (hok : o.ok = false)
    (h : o.out <+: helloMsg) : DInv o d.trapped := ⟨hok, h⟩

theorem dinv_run {o : Obs} {d : DConf helloK} (c : HConf) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (h : PcInv o c) :
    DInv o { d with core := c } := by
  refine ⟨hok, ?_⟩
  simp only [hm]
  exact .inl ⟨hr, h⟩

theorem dinv_run_trapped {o : Obs} {d : DConf helloK} (c : HConf) (hm : d.mode = .run)
    (hok : o.ok = false) (hc : c.pc = .trapped) (h : o.out <+: helloMsg) :
    DInv o { d with core := c } := by
  refine ⟨hok, ?_⟩
  simp only [hm]
  exact .inr (.inr ⟨hc, h⟩)

/-- The answer of a quiet call: the observations do not change; the continuation either traps or
resumes `helloK` with `afterCall`. -/
theorem resume_quiet {o : Obs} {d : DConf helloK} {c' : HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpre : o.out <+: helloMsg)
    (hc' : c'.pc = .trapped ∨ PcInv o c') :
    DInv o { d with core := c' } := by
  rcases hc' with h | h
  · exact dinv_run_trapped c' hm hok h hpre
  · exact dinv_run c' hm hok hr h

/-! ## The OS image on the events of `hello` -/

theorem os_out_nil {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cWait) (q : OsSt) (a r) :
    (osStep3 0 q (.imp f a r)).2 = [] := by
  unfold osStep3
  dsimp only
  simp only [h1, h2, ite_false]
  split_ifs <;> (repeat' split) <;> rfl

theorem os_write (q : OsSt) {w : Nat} (bs : List (BitVec 8)) (pv : Val) (hw : w < 2 ^ 32) :
    osStep3 0 q (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      match (natOf pv).bind copyOf with
      | some (some (.completed, k)) => (q, if w ∈ q.outW then (bs.take k).map (.writeEv 0) else [])
      | some none => ({ q with pend := (w, bs) :: q.pend }, [])
      | _ => (q, []) := by
  unfold osStep3
  dsimp only
  simp only [show cStreamWrite ≠ cStreamNew by decide, show cStreamWrite ≠ stdoutWrite3 by decide,
    ite_false, ite_true, natOf_natV hw, bytesOf_bytesV, Option.bind_eq_bind]
  generalize (natOf pv).bind copyOf = x
  rcases x with _ | _ | ⟨r, k⟩
  · rfl
  · rfl
  · cases r <;> by_cases hw' : w ∈ q.outW <;> simp [hw']

theorem natOf_lt {v : Val} {n : Nat} (h : natOf v = some n) : n < 2 ^ 32 := by
  cases v <;> simp only [natOf, reduceCtorEq, Option.some.injEq] at h
  rw [← h]; exact BitVec.isLt _

theorem copyOf_blocked {n : Nat} : copyOf n = some none ↔ n = blocked := by
  unfold copyOf
  constructor
  · intro h; split_ifs at h <;> simp_all
  · intro h; simp [h]

theorem natOf_u32 {v : Val} {n : Nat} (h : natOf v = some n) : v = natV n := by
  cases v <;> simp only [natOf, reduceCtorEq, Option.some.injEq] at h
  rw [← h]; simp only [natV, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The continuation of a forwarded built-in (`DCall.fwd`). -/
abbrev contOf (d : DConf helloK) (kont : Option (List Val) → Option HConf) (n : Option (List Val)) :
    DConf helloK := contWith d kont n

theorem contOf_none {d : DConf helloK} {kont : Option (List Val) → Option HConf}
    {n : Option (List Val)} (h : kont n = none) : contOf d kont n = d.trapped := by
  simp only [contOf, contWith, h]

theorem contOf_some {d : DConf helloK} {kont : Option (List Val) → Option HConf}
    {n : Option (List Val)} {y : HConf} (h : kont n = some y) :
    contOf d kont n = { d with core := y } := by
  simp only [contOf, contWith, h]

/-! ## The program points -/

/-- The call of a program point, from `callOf`. -/
theorem call_eq {c : HConf} {k' k0 : Nat} {args a0 : List Nat} (hc : callOf c = some (k0, a0))
    (hco : callOf c = some (k', args)) : k' = k0 ∧ args = a0 := by
  rw [hc] at hco; simpa only [Option.some.injEq, Prod.mk.injEq] using hco.symm

theorem waitStep_other {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cWait) (q : List Nat)
    (a : List Val) (r : Option (List Val)) : waitStep q (.imp f a r) = some q := by
  simp only [waitStep, h1, h2, ite_false]

theorem obsStep_noemit {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cWait) (o : Obs)
    (a : List Val) (r : Option (List Val)) :
    obsStep o (.imp f a r) = { o with os := (osStep3 0 o.os (.imp f a r)).1 } := by
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, os_out_nil h1 h2, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false, waitStep_other h1 h2]
  cases wp <;> rfl

theorem os_new (q : OsSt) {rv wv : Val} {r w : Nat} (hr : natOf rv = some r) (hw : natOf wv = some w) :
    osStep3 0 q (.imp cStreamNew [] (some [rv, wv])) = ({ q with pairs := (r, w) :: q.pairs }, []) := by
  unfold osStep3
  simp only [ite_true, hr, hw]

theorem os_wvs (q : OsSt) (rv : Val) (r : Option (List Val)) :
    osStep3 0 q (.imp stdoutWrite3 [rv] r) =
      match (natOf rv).bind (fun r' => (q.pairs.find? (·.1 = r')).map (·.2)) with
      | some w' => ({ q with outW := w' :: q.outW }, [])
      | none => (q, []) := by
  unfold osStep3
  simp only [show stdoutWrite3 ≠ cStreamNew by decide, ite_false, ite_true, Option.bind_eq_bind]
  split <;> rename_i h <;> simp only [h]

theorem pack_mod {r w : Nat} (hr : r < 2 ^ 32) : packEnds r w % 2 ^ 32 = r := by
  simp only [packEnds, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem pack_div {r w : Nat} (hr : r < 2 ^ 32) : packEnds r w / 2 ^ 32 = w := by
  simp only [packEnds, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hr,
    Nat.zero_add]

theorem cStreamNew_ne₁ : cStreamNew ≠ cStreamWrite := by decide
theorem cStreamNew_ne₂ : cStreamNew ≠ cWait := by decide
theorem stdoutWrite3_ne₁ : stdoutWrite3 ≠ cStreamWrite := by decide
theorem stdoutWrite3_ne₂ : stdoutWrite3 ≠ cWait := by decide

/-- After `stream.new` answered `r, w`. -/
theorem new_next {o : Obs} {c : HConf} {r w : Nat} (hpc : c.pc = .new) (hr : r < 2 ^ 32)
    (hw : w < 2 ^ 32) (hp : o.out = [] ∧ o.os = {} ∧ o.wp = some [] ∧ c.off = 0) :
    PcInv { o with os := ({ o.os with pairs := (r, w) :: o.os.pairs } : OsSt) }
      (afterCall c [packEnds r w]) := by
  simp only [afterCall, hpc, PcInv, pack_mod hr, pack_div hr]
  refine ⟨hp.1, ?_, ?_, hr, hw, hp.2.2.1, hp.2.2.2⟩ <;> simp [hp.2.1]

theorem resume_new {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .new)
    (hp : o.out = [] ∧ o.os = {} ∧ o.wp = some [] ∧ d.core.off = 0)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 7) (a0 := []) (by simp only [callOf, hpc]) hco
  simp only [hw.streamNew, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  show DInv (obsStep o (.imp cStreamNew [] n)) _
  rw [obsStep_noemit cStreamNew_ne₁ cStreamNew_ne₂]
  have htrap : ∀ os : OsSt, DInv { o with os := os } d.trapped := fun _ =>
    dinv_trapped hok (by show o.out <+: _; rw [hp.1]; exact List.nil_prefix)
  rcases n with _ | ⟨_ | ⟨rv, _ | ⟨wv, _ | _⟩⟩⟩
  rotate_left 3
  · cases hrv : natOf rv <;> cases hwv : natOf wv <;> simp only [contOf, contWith, hrv, hwv]
    all_goals try exact htrap _
    rw [os_new _ hrv hwv]
    exact dinv_run _ hm hok hr (new_next hpc (natOf_lt hrv) (natOf_lt hwv) hp)
  all_goals exact htrap _

theorem resume_wsNew {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .wsNew)
    (hp : Live o d.core ∧ d.core.off < len ∧ o.wp = some [])
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 3) (a0 := []) (by simp only [callOf, hpc]) hco
  simp only [hw.wsNew, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  show DInv (obsStep o (.imp cWsNew [] n)) _
  rw [obsStep_quiet quiet_wsNew]
  have htrap : DInv o d.trapped := dinv_trapped hok hp.1.prefix
  rcases n with _ | ⟨_ | ⟨sv, _ | _⟩⟩
  · exact htrap
  · exact htrap
  · cases hs : natOf sv with
    | none => simp only [contOf, contWith, hs, Option.map_none]; exact htrap
    | some sn =>
      simp only [contOf, contWith, hs, Option.map_some]
      refine dinv_run _ hm hok hr ?_
      simp only [helloK, afterCall, hpc]
      exact hp
  · exact htrap

/-- A built-in answered by `[]`, with a quiet event: `afterCall c []` keeps the invariant. -/
theorem resume_unit {o : Obs} {d : DConf helloK} {f : FnName} {a : List Val}
    {n : Option (List Val)} (hq : Quiet f) (hm : d.mode = .run) (hok : o.ok = false)
    (hr : d.result = none) (hpre : o.out <+: helloMsg) (hnext : PcInv o (afterCall d.core [])) :
    DInv (obsStep o (.imp f a n))
      (contOf d (fun | some [] => some (helloK.resume d.core []) | _ => none) n) := by
  rw [obsStep_quiet hq]
  have htrap : DInv o d.trapped := dinv_trapped hok hpre
  rcases n with _ | ⟨_ | ⟨_, _⟩⟩
  · exact htrap
  · exact dinv_run _ hm hok hr hnext
  · exact htrap

theorem resume_joinW {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .joinW) (hp : Blocked o d.core)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 4) (a0 := [d.core.w, d.core.s]) (by simp only [callOf, hpc]) hco
  simp only [hw.join, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  refine resume_unit quiet_join hm hok hr hp.1.prefix ?_
  simp only [afterCall, hpc]
  exact hp

theorem resume_joinF {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .joinF) (hp : Done o d.core)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 4) (a0 := [d.core.f, d.core.s]) (by simp only [callOf, hpc]) hco
  simp only [hw.join, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  refine resume_unit quiet_join hm hok hr hp.1.prefix ?_
  simp only [afterCall, hpc]
  exact hp

theorem resume_dropW {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .dropW) (hp : Done o d.core)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 19) (a0 := [d.core.w]) (by simp only [callOf, hpc]) hco
  simp only [hw.dropW, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  refine resume_unit quiet_dropW hm hok hr hp.1.prefix ?_
  simp only [afterCall, hpc]
  exact hp

/-- `afterRead` after all bytes are out keeps the invariant. -/
theorem afterRead_inv {o : Obs} {c : HConf} (code : Nat) (hp : Done o c) :
    PcInv o (afterRead c code) := by
  have hret : ∀ v, PcInv o { c with pc := .ret v } := fun _ => ⟨hp.1, fun _ => hp.2.1, hp.2.2⟩
  unfold afterRead
  split
  · exact hp
  · exact hret _
  · exact hret _

theorem resume_fread {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .fread) (hp : Done o d.core)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 26) (a0 := [d.core.f, 64]) (by simp only [callOf, hpc]) hco
  simp only [hw.fread, forward] at hf
  obtain ⟨rfl, rfl⟩ := hf
  show DInv (obsStep o (.imp cFutureRead _ n)) _
  rw [obsStep_quiet quiet_fread]
  have htrap : DInv o d.trapped := dinv_trapped hok hp.1.prefix
  have hnext : ∀ (c : HConf) (code : Nat), c.pc = .fread → Done o c →
      DInv o { d with core := afterCall c [code] } := fun c code hc hd =>
    dinv_run _ hm hok hr (by simp only [afterCall, hc]; exact afterRead_inv code hd)
  rcases n with _ | ⟨_ | ⟨pv, _ | ⟨v, _ | _⟩⟩⟩
  rotate_left 2
  · cases hs : natOf pv with
    | none => simp only [contOf, contWith, hs, Option.map_none]; exact htrap
    | some code => simp only [contOf, contWith, hs, Option.map_some]; exact hnext _ code hpc hp
  · cases hs : natOf pv with
    | none => simp only [contOf, contWith, hs]; exact htrap
    | some code => simp only [contOf, contWith, hs, helloK, Option.map_some]; exact hnext _ code hpc hp
  all_goals exact htrap

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
