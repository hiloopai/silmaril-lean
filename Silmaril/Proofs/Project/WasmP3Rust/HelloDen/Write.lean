module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Resume

/-!
# `hello` under `den`: the answers to `write-via-stream` and `stream.write`
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-- The OS image after `write-via-stream(r)` in `wvs`. -/
theorem os_wvs_eq {o : Obs} {c : HConf} (n : Option (List Val))
    (hp : o.os.outW = [] ∧ (o.os.pairs.find? (·.1 = c.r)).map (·.2) = some c.w ∧ c.r < 2 ^ 32) :
    (osStep3 0 o.os (.imp stdoutWrite3 [natV c.r] n)).1 = { o.os with outW := [c.w] } := by
  rw [os_wvs, natOf_natV hp.2.2]
  simp only [Option.bind_some, hp.2.1, hp.1]

/-- The continuation of `write-via-stream`: a trap, or `afterCall` with the future. -/
theorem wvs_kont {x : HConf} {f : {f // f ∈ p3World.imports}} {r : Nat} {m : P3Op}
    {kont : Option (List Val) → Option HConf} (hpc : x.pc = .wvs)
    (hf : forward helloK (.wasi f) [r] x = some (m, kont)) (n : Option (List Val)) (y : HConf)
    (hy : kont n = some y) : y.pc = .trapped ∨ ∃ fv, y = afterCall x [fv] := by
  simp only [forward] at hf
  obtain ⟨-, rfl⟩ := hf
  beta_reduce at hy
  split at hy
  · cases hy; exact .inl (by simp only [helloK, afterCall, hpc])
  · split at hy
    · cases hy; exact .inl (by simp only [helloK, afterCall, hpc])
    · exact absurd hy (by simp)
  · obtain ⟨fv, -, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact .inr ⟨fv, rfl⟩
  · exact absurd hy (by simp)

/-- A continuation that traps or resumes into a configuration with the invariant. -/
theorem cont_inv {o : Obs} {d : DConf helloK} {kont : Option (List Val) → Option HConf}
    {n : Option (List Val)} (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none)
    (hpre : o.out <+: helloMsg) (hk : ∀ y, kont n = some y → y.pc = .trapped ∨ PcInv o y) :
    DInv o (contOf d kont n) := by
  simp only [contOf, contWith]
  split
  · rename_i y hy; exact resume_quiet hm hok hr hpre (hk y hy)
  · exact dinv_trapped hok hpre

theorem resume_wvs {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .wvs)
    (hp : o.out = [] ∧ o.os.outW = [] ∧ (o.os.pairs.find? (·.1 = d.core.r)).map (·.2) = some d.core.w ∧
      d.core.r < 2 ^ 32 ∧ d.core.w < 2 ^ 32 ∧ o.wp = some [] ∧ d.core.off = 0)
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 21) (a0 := [d.core.r]) (by simp only [callOf, hpc]) hco
  rw [hw.wvs] at hf
  have hk := wvs_kont hpc hf n
  simp only [forward] at hf
  obtain ⟨rfl, -⟩ := hf
  show DInv (obsStep o (.imp stdoutWrite3 [natV d.core.r] n)) _
  rw [obsStep_noemit stdoutWrite3_ne₁ stdoutWrite3_ne₂, os_wvs_eq n ⟨hp.2.1, hp.2.2.1, hp.2.2.2.1⟩]
  refine cont_inv hm hok hr (by show o.out <+: _; rw [hp.1]; exact List.nil_prefix) fun y hy => ?_
  rcases hk y hy with h | ⟨fv, rfl⟩
  · exact .inl h
  · refine .inr ?_
    simp only [afterCall, hpc, PcInv, Live]
    refine ⟨⟨?_, hp.2.2.2.2.1, ?_, ?_⟩, ?_, hp.2.2.2.2.2.1⟩ <;> simp [hp.1, hp.2.2.2.2.2.2, len]

theorem wbytes_map (l : List (BitVec 8)) : wbytes (l.map (.writeEv 0)) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, wbytes, List.filterMap_cons] at ih ⊢; rw [ih]

theorem os_write_other (q : OsSt) (a : List Val) (n : Option (List Val))
    (hn : ∀ pv, n ≠ some [pv]) : osStep3 0 q (.imp cStreamWrite a n) = (q, []) := by
  unfold osStep3
  dsimp only
  simp only [show cStreamWrite ≠ cStreamNew by decide, show cStreamWrite ≠ stdoutWrite3 by decide,
    ite_false, ite_true]
  split
  · exact absurd rfl (hn _)
  · rfl

/-- `advance` keeps the invariant when the `k` bytes after `off` came out. -/
theorem advance_inv {o : Obs} {c : HConf} (k : Nat) (hl : Live o c)
    (hwp : o.wp = some []) :
    PcInv { o with out := helloMsg.take c.off ++ (helloMsg.drop c.off).take k } (advance c k) := by
  rw [take_add_drop]
  unfold advance
  split
  · rename_i h
    exact ⟨⟨hl.1, hl.2.1, rfl, (show c.off + k ≤ len by omega)⟩, h, hwp⟩
  · rename_i h
    exact ⟨⟨hl.1, hl.2.1, by rw [take_ge (by omega), take_len], le_refl _⟩, rfl, hwp⟩


theorem take_drop_len (off : Nat) : (helloMsg.drop off).take (len - off) = helloMsg.drop off := by
  have hl : (helloMsg.drop off).length = len - off := by rw [List.length_drop, helloMsg_length]
  rw [List.take_of_length_le (Nat.le_of_eq hl)]

theorem wait_write_blocked {q : List Nat} {w : Nat} {pv : Val} (bs : List (BitVec 8)) (hw : w < 2 ^ 32)
    (hb : natOf pv = some blocked) :
    waitStep q (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) = some (w :: q) := by
  simp only [waitStep, ite_true, hb, natOf_natV hw]

theorem wait_write_other {q : List Nat} {w : Nat} {pv : Val} (bs : List (BitVec 8))
    (hb : natOf pv ≠ some blocked) :
    waitStep q (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) = some q := by
  simp only [waitStep, ite_true, hb, ite_false]

theorem copyOf_ne_blocked {code : Nat} {r : Option (CopyResult × Nat)} (h : copyOf code = some r)
    (hr : r ≠ none) : some code ≠ some blocked := fun e => by
  rw [Option.some.injEq] at e
  rw [e, copyOf_blocked.2 rfl, Option.some.injEq] at h
  exact hr h.symm

theorem obsStep_write_other (o : Obs) (a : List Val) (n : Option (List Val))
    (hn : ∀ pv, n ≠ some [pv]) : obsStep o (.imp cStreamWrite a n) = o := by
  have hw : ∀ q, waitStep q (.imp cStreamWrite a n) = some q := fun q => by
    unfold waitStep
    simp only [ite_true]
    split
    · exact absurd rfl (hn _)
    · rfl
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, os_write_other os a n hn, hw, wbytes, List.filterMap_nil, List.append_nil,
    okEv, Bool.or_false]
  cases wp <;> rfl

/-- A write answered with a packed code other than `BLOCKED` and `COMPLETED`. -/
theorem obsStep_write_none (o : Obs) {w : Nat} (bs : List (BitVec 8)) {pv : Val} (hw : w < 2 ^ 32)
    (hc : ∀ k, (natOf pv).bind copyOf ≠ some (some (.completed, k)))
    (hb : (natOf pv).bind copyOf ≠ some none) :
    obsStep o (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) = o := by
  have hnb : natOf pv ≠ some blocked := fun e => hb (by rw [e]; exact copyOf_blocked.2 rfl)
  have hos : osStep3 0 o.os (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) = (o.os, []) := by
    rw [os_write _ _ _ hw]
    split
    · rename_i k h; exact absurd h (hc k)
    · rename_i h; exact absurd h hb
    · rfl
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, hos, wait_write_other bs hnb, wbytes, List.filterMap_nil, List.append_nil,
    okEv, Bool.or_false]
  cases wp <;> rfl

theorem obsStep_write_blocked (o : Obs) {w : Nat} (bs : List (BitVec 8)) {pv : Val}
    (hw : w < 2 ^ 32) (hb : natOf pv = some blocked) :
    obsStep o (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      { o with os := { o.os with pend := (w, bs) :: o.os.pend },
               wp := o.wp.bind fun q => some (w :: q) } := by
  have hc : (natOf pv).bind copyOf = some none := by rw [hb]; exact copyOf_blocked.2 rfl
  have hos : osStep3 0 o.os (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      ({ o.os with pend := (w, bs) :: o.os.pend }, []) := by
    rw [os_write _ _ _ hw, hc]
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, hos, wait_write_blocked bs hw hb, wbytes, List.filterMap_nil,
    List.append_nil, okEv, Bool.or_false]

theorem obsStep_write_completed (o : Obs) {w k : Nat} (bs : List (BitVec 8)) {pv : Val}
    (hw : w < 2 ^ 32) (hc : (natOf pv).bind copyOf = some (some (.completed, k)))
    (hout : w ∈ o.os.outW) :
    obsStep o (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      { o with out := o.out ++ bs.take k } := by
  have hnb : natOf pv ≠ some blocked := fun e => by
    rw [e, Option.bind_some, copyOf_blocked.2 rfl] at hc; cases hc
  have hos : osStep3 0 o.os (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      (o.os, (bs.take k).map (.writeEv 0)) := by
    rw [os_write _ _ _ hw, hc]; simp only [hout, ite_true]
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, hos, wait_write_other bs hnb, wbytes_map, okEv, Bool.or_false]
  cases wp <;> rfl

/-- A write answered with the packed code `code`. -/
theorem write_code {o : Obs} {d : DConf helloK} {pv : Val} {code : Nat} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .write)
    (hp : Live o d.core ∧ d.core.off < len ∧ o.wp = some []) (hww : d.core.w < 2 ^ 32)
    (hret1 : PcInv o { d.core with pc := .ret 1 })
    (hpv : natOf pv = some code) :
    DInv (obsStep o (.imp cStreamWrite [natV d.core.w, bytesV (helloMsg.drop d.core.off)]
      (some [pv])))
      (contOf d (fun x => match x with
        | some [pv] => Option.map (fun c => helloK.resume d.core [c]) (natOf pv)
        | _ => none) (some [pv])) := by
  have hac : helloK.resume d.core [code] = afterWrite d.core code := by
    simp only [helloK, afterCall, hpc]
  simp only [contOf, contWith, hpv]
  show DInv _ { d with core := helloK.resume d.core [code] }
  rw [hac]
  rcases hc : copyOf code with _ | _ | ⟨_ | _ | _, k⟩
  · rw [obsStep_write_none _ _ hww (by simp [hpv, hc]) (by simp [hpv, hc])]
    exact dinv_run _ hm hok hr (by simp only [afterWrite, hc]; exact hret1)
  · rw [obsStep_write_blocked _ _ hww (by rw [hpv, copyOf_blocked.1 hc])]
    refine dinv_run _ hm hok hr ?_
    simp only [afterWrite, hc, PcInv, Blocked, hp.2.2, Option.bind_some]
    refine ⟨hp.1, hp.2.1, ?_, ?_⟩ <;> simp
  · rw [obsStep_write_completed (k := k) _ _ hww (by simp [hpv, hc]) (by rw [hp.1.1]; simp)]
    refine dinv_run _ hm hok hr ?_
    simp only [afterWrite, hc]
    have e : ({ o with out := o.out ++ (helloMsg.drop d.core.off).take k } : Obs) =
        { o with out := helloMsg.take d.core.off ++ (helloMsg.drop d.core.off).take k } := by
      rw [hp.1.2.2.1]
    rw [e]
    exact advance_inv k hp.1 hp.2.2
  · rw [obsStep_write_none _ _ hww (by simp [hpv, hc]) (by simp [hpv, hc])]
    exact dinv_run _ hm hok hr (by simp only [afterWrite, hc]; exact hret1)
  · rw [obsStep_write_none _ _ hww (by simp [hpv, hc]) (by simp [hpv, hc])]
    exact dinv_run _ hm hok hr (by simp only [afterWrite, hc]; exact hret1)

theorem resume_write {S : Spaces} (hw : HelloWiring S) {o : Obs} {d : DConf helloK} {k' : Nat}
    {args : List Nat} {m : P3Op} {kont : Option (List Val) → Option HConf} (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .write)
    (hp : Live o d.core ∧ d.core.off < len ∧ o.wp = some [])
    (hco : callOf d.core = some (k', args))
    (hf : forward helloK (builtin S k') args d.core = some (m, kont)) (n : Option (List Val)) :
    DInv (obsStep o (.imp m.1.1 m.2 n)) (contOf d kont n) := by
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := 27) (a0 := [d.core.w, d.core.off, len - d.core.off])
    (by simp only [callOf, hpc]) hco
  rw [hw.write] at hf
  simp only [forward, helloK, take_drop_len, Option.map_some, Option.some.injEq] at hf
  obtain ⟨rfl, rfl⟩ := hf
  show DInv (obsStep o (.imp cStreamWrite [natV d.core.w, bytesV (helloMsg.drop d.core.off)] n)) _
  have hww : d.core.w < 2 ^ 32 := hp.1.2.1
  have htrap : DInv o d.trapped := dinv_trapped hok hp.1.prefix
  have hret1 : PcInv o { d.core with pc := .ret 1 } := ⟨hp.1, nofun, hp.2.2⟩
  rcases n with _ | ⟨_ | ⟨pv, _ | _⟩⟩
  · rw [obsStep_write_other _ _ _ (by simp)]; exact htrap
  · rw [obsStep_write_other _ _ _ (by simp)]; exact htrap
  · cases hpv : natOf pv with
    | none =>
      rw [obsStep_write_none _ _ hww (by simp [hpv]) (by simp [hpv])]
      simp only [contOf, contWith, hpv, Option.map_none]; exact htrap
    | some code => exact write_code hm hok hr hpc hp hww hret1 hpv
  · rw [obsStep_write_other _ _ _ (by simp)]; exact htrap

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
