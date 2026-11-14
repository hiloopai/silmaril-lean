module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Loop

/-!
# `cat` and `echo` under `DenX.den`: reading stdin and writing stdout

`gotChunk_inv` (a read delivered a chunk: stdin's bytes grew by exactly the chunk, and stdout
is behind by it), `advance_inv` (a write accepted `k` more bytes), and the answers of
`stream.read` (`resume_read`) and `stream.write` (`resume_write`).
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

theorem wbytes_map (l : List (BitVec 8)) : wbytes (l.map (.writeEv 0)) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, wbytes, List.filterMap_cons] at ih ⊢; rw [ih]

theorem copyCount_of {code : Nat} {r : CopyResult} {k : Nat} (h : copyOf code = some (some (r, k))) :
    copyCount code = some k := by
  simp only [copyCount, h]

theorem copyCount_none {code : Nat} (h : ∀ r k, copyOf code ≠ some (some (r, k))) :
    copyCount code = none := by
  unfold copyCount
  split
  · rename_i r k hc; exact absurd hc (h r k)
  · rfl

/-! ## Chunks -/

/-- `Live` only reads the stdout bytes, the OS image's writable ends, the target and stdin's
ends. -/
theorem Live.congr {o o' : Obs} {c : SConf} (h : Live P o c) (hout : o'.out = o.out)
    (hw : o'.os.outW = o.os.outW) (ht : tgt P o' = tgt P o) (hrs : o'.rs = o.rs) : Live P o' c := by
  obtain ⟨h1, h2, ⟨⟨m, hm, he⟩, hle⟩, h4⟩ := h
  refine ⟨hw ▸ h1, h2, ⟨⟨m, ht ▸ hm, hout ▸ he⟩, hle⟩, ?_⟩
  unfold Src at h4 ⊢
  rw [hrs]; exact h4

/-- **A read delivered a chunk**: with the previous chunk out, stdout is behind stdin by exactly
the new chunk. -/
theorem gotChunk_inv {o o' : Obs} {d : DConf (stdioK P)} {c : SConf} {res : CopyResult} {k : Nat}
    (hk : P.kind = .cat) (hl : Live P o c) (hoff : c.off = c.chunk.length)
    (hout : o'.out = o.out) (hos : o'.os = o.os) (hrs : o'.rs = o.rs)
    (hinp : o'.inp = o.inp ++ c.buf.take k) (hwp : o'.wp = some ([], [])) (hpend : d.pend = []) :
    PcInv P o' { d with core := gotChunk P c res k } := by
  unfold gotChunk
  refine startChunk_inv ?_ hwp hpend
  obtain ⟨h1, h2, ⟨⟨m, hm, he⟩, -⟩, h4⟩ := hl
  simp only [tgt, hk, Option.some.injEq] at hm
  subst hm
  rw [hoff, List.drop_length, List.append_nil] at he
  refine ⟨hos ▸ h1, h2, ⟨⟨o'.inp, by simp only [tgt, hk], ?_⟩, by simp⟩, ?_⟩
  · simp only [List.drop_zero, hout, he, hinp]
  · unfold Src at h4 ⊢; rw [hrs]; exact h4

/-- **A write accepted `k` more bytes of the chunk.** -/
theorem advance_inv {o o' : Obs} {d : DConf (stdioK P)} {c : SConf} {k : Nat} (hl : Live P o c)
    (hout : o'.out = o.out ++ (c.chunk.drop c.off).take k)
    (hw : o'.os.outW = o.os.outW) (ht : tgt P o' = tgt P o) (hrs : o'.rs = o.rs)
    (hwp : o'.wp = some ([], [])) (hpend : d.pend = []) :
    PcInv P o' { d with core := advance P c k } := by
  obtain ⟨h1, h2, ⟨⟨m, hm, he⟩, hle⟩, h4⟩ := hl
  have hsrc : Src P o' c := by unfold Src at h4 ⊢; rw [hrs]; exact h4
  unfold advance
  split
  · rename_i hk
    simp only [PcInv]
    refine ⟨⟨hw ▸ h1, h2, ⟨⟨m, ht ▸ hm, ?_⟩, by simp only; omega⟩, hsrc⟩, hk, hwp, hpend⟩
    simp only [hout, List.append_assoc, ← he]
    congr 1
    rw [← List.drop_drop, List.take_append_drop]
  · rename_i hk
    refine afterChunk_inv ⟨hw ▸ h1, h2, ⟨⟨m, ht ▸ hm, ?_⟩, by simp⟩, hsrc⟩ rfl hwp hpend
    simp only [List.drop_length, List.append_nil, hout, ← he]
    congr 1
    rw [List.take_of_length_le (by simp; omega)]

/-- A write that failed: `cat` returns `error` (`ret 1`), `echo` traps. -/
theorem failWrite_inv {o : Obs} {d : DConf (stdioK P)} {c : SConf} (hl : Live P o c)
    (hwp : o.wp = some ([], [])) (hpend : d.pend = []) (hm : d.mode = .run) (hok : o.ok = false)
    (hr : d.result = none) : DInv P o { d with core := failWrite P c } := by
  unfold failWrite
  split
  · refine dinv_run hm hok hr ?_
    simp only [PcInv]
    refine ⟨hl, fun h => absurd h (by decide), hwp, ?_⟩
    rw [hpend]; exact fun _ h => absurd h List.not_mem_nil
  · exact dinv_run_trapped hm hok rfl hl.prefOk

/-! ## The events of `stream.read` and `stream.write` -/

theorem obsStep_read {o : Obs} {r : Nat} (hr : r < 2 ^ 32) (hrs : o.rs = [r]) (pv items : Val)
    {code : Nat} (hc : natOf pv = some code) :
    obsStep o (.imp cStreamRead [natV r, natV bufN] (some [pv, items])) =
      { o with wp := o.wp.bind (fun q => some (if code = blocked then (q.1, r :: q.2) else q)),
               inp := o.inp ++ ((copyCount code).map fun k => (bytesOf items).take k).getD [] } := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  simp only at hrs
  subst hrs
  have h1 : osStep3 0 os (.imp cStreamRead [natV r, natV bufN] (some [pv, items])) = (os, []) :=
    os_quiet (by decide) (by decide) (by decide) (by decide) _ _ _
  have h2 : ∀ q, waitStepX q (.imp cStreamRead [natV r, natV bufN] (some [pv, items])) =
      some (if code = blocked then (q.1, r :: q.2) else q) := by
    intro q
    simp only [waitStepX, show cStreamRead ≠ cStreamWrite by decide, ite_false, ite_true, hc,
      natOf_natV hr, Option.some.injEq]
    split <;> rfl
  have h3 : inStep [r] (.imp cStreamRead [natV r, natV bufN] (some [pv, items])) =
      ([r], ((copyCount code).map fun k => (bytesOf items).take k).getD []) := by
    rcases hcc : copyCount code with _ | k
    all_goals
      unfold inStep
      simp only [show cStreamRead ≠ stdinRead3 by decide, ite_false, ite_true, natOf_natV hr, hc,
        Option.bind_eq_bind, Option.bind_some, hcc, List.mem_singleton, Option.map_none,
        Option.getD_none, Option.map_some, Option.getD_some]
  simp only [obsStep, h1, h2, h3, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false, argsStep_other (show cStreamRead ≠ getArgs3 by decide)]

theorem obsStep_read_out (o : Obs) (a : List Val) (n : Option (List Val)) :
    (obsStep o (.imp cStreamRead a n)).out = o.out ∧ (obsStep o (.imp cStreamRead a n)).args = o.args ∧
      o.inp <+: (obsStep o (.imp cStreamRead a n)).inp := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [obsStep, os_quiet (show cStreamRead ≠ cStreamNew by decide) (by decide) (by decide)
      (by decide), wbytes, List.filterMap_nil, List.append_nil]
  · simp only [obsStep, argsStep_other (show cStreamRead ≠ getArgs3 by decide)]
  · exact List.prefix_append _ _

theorem obsStep_ok_imp (o : Obs) (f : FnName) (a : List Val) (r : Option (List Val)) :
    (obsStep o (.imp f a r)).ok = o.ok := by
  simp only [obsStep, okEv, Bool.or_false]

theorem prefOk_of_cat {o o' : Obs} (hk : P.kind = .cat) (hout : o'.out = o.out)
    (hinp : o.inp <+: o'.inp) (h : PrefOk P o) : PrefOk P o' := by
  simp only [PrefOk, tgt, hk] at h ⊢
  rw [hout]; exact h.trans hinp

theorem resume_read {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .read)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨⟨hl, hoff, hwp⟩, hpend, hk⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.read) (a0 := [d.core.rin, 0, bufN])
    (by simp only [callOf, hpc]) hco
  rw [hw.read] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  show DInv P (obsStep o (.imp cStreamRead [natV d.core.rin, natV bufN] n)) _
  have hsrc := hl.2.2.2
  simp only [Src, hk] at hsrc
  obtain ⟨hrs, hr32⟩ := hsrc
  cases hkn : kont n with
  | none =>
    rw [contWith_none hkn]
    obtain ⟨h1, -, h3⟩ := obsStep_read_out o [natV d.core.rin, natV bufN] n
    exact dinv_trapped (by rw [obsStep_ok_imp]; exact hok) (prefOk_of_cat hk h1 h3 hl.prefOk)
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i pv items
      cases hc : natOf pv with
      | none => simp only [hc] at hkn; cases hkn
      | some code =>
        simp only [hc, dstore, Option.map_some, Option.some.injEq] at hkn
        subst hkn
        rw [obsStep_read hr32 hrs pv items hc]
        have hst : store d.core 0 (bytesOf items) = { d.core with buf := bytesOf items } := by
          simp [store]
        cases hcp : copyOf code with
        | none =>
          have hnb : code ≠ blocked := fun e => by rw [e] at hcp; simp [copyOf] at hcp
          have hcc : copyCount code = none := copyCount_none fun r k e => by rw [hcp] at e; cases e
          simp only [hnb, ite_false, hcc, Option.map_none, Option.getD_none, List.append_nil]
          refine dinv_run hm hok hr ?_
          simp only [PcInv, dresume, hst, afterCall, hpc, afterRead, hcp]
          refine ⟨hl.congr rfl rfl rfl rfl, fun h => absurd h (by decide), by rw [hwp]; rfl, ?_⟩
          rw [hpend]; exact fun _ h => absurd h List.not_mem_nil
        | some x =>
          rcases x with _ | ⟨res, k⟩
          · have hb : code = blocked := copyOf_blocked.1 hcp
            have hcc : copyCount code = none := copyCount_none fun r k e => by rw [hcp] at e; cases e
            subst hb
            simp only [ite_true, hcc, Option.map_none, Option.getD_none, List.append_nil]
            refine dinv_run hm hok hr ?_
            simp only [PcInv, dresume, DConf.block, hst, afterCall, hpc, afterRead, hcp, hwp,
              Option.bind_some, hpend]
            exact ⟨hl.congr rfl rfl rfl rfl, hoff, trivial, trivial, hk⟩
          · have hnb : code ≠ blocked := fun e => by
              rw [e, copyOf_blocked.2 rfl] at hcp; cases hcp
            simp only [hnb, ite_false, copyCount_of hcp, Option.map_some, Option.getD_some]
            refine dinv_run hm hok hr ?_
            simp only [dresume, hst, afterCall, hpc, afterRead, hcp]
            exact gotChunk_inv (o := o) hk hl hoff rfl rfl rfl rfl (by rw [hwp]; rfl) hpend
    · cases hkn

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

theorem os_write_other (q : OsSt) (a : List Val) (n : Option (List Val))
    (h : ∀ pv, n = some [pv] → natOf pv = none) :
    (osStep3 0 q (.imp cStreamWrite a n)).2 = [] := by
  unfold osStep3
  dsimp only
  simp only [show cStreamWrite ≠ cStreamNew by decide, show cStreamWrite ≠ stdoutWrite3 by decide,
    ite_false, ite_true]
  split
  · rename_i wv buf pv
    rw [h pv rfl]
    simp
  · rfl

theorem obsStep_write {o : Obs} {w : Nat} (hw : w < 2 ^ 32) (bs : List (BitVec 8)) (pv : Val)
    {code : Nat} (hc : natOf pv = some code) :
    obsStep o (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      { o with os := (osStep3 0 o.os (.imp cStreamWrite [natV w, bytesV bs] (some [pv]))).1,
               out := o.out ++ wbytes (osStep3 0 o.os (.imp cStreamWrite [natV w, bytesV bs]
                 (some [pv]))).2,
               wp := o.wp.bind (fun q => some (if code = blocked then (w :: q.1, q.2) else q)) } := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  have h2 : ∀ q, waitStepX q (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) =
      some (if code = blocked then (w :: q.1, q.2) else q) := by
    intro q
    simp only [waitStepX, ite_true, hc, natOf_natV hw, Option.some.injEq]
    split <;> rfl
  have h3 : inStep rs (.imp cStreamWrite [natV w, bytesV bs] (some [pv])) = (rs, []) :=
    inStep_quiet (by decide) (by decide) (by decide) _ _ _
  simp only [obsStep, h2, h3, okEv, Bool.or_false, List.append_nil,
    argsStep_other (show cStreamWrite ≠ getArgs3 by decide)]

theorem resume_write {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hm : d.mode = .run)
    (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .write)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hl, hlt, hwp, hpend⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.write)
    (a0 := [d.core.w, d.core.off, d.core.chunk.length - d.core.off]) (by simp only [callOf, hpc]) hco
  rw [hw.write] at hf
  simp only [forward, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  have hbs : (d.core.chunk.drop d.core.off).take (d.core.chunk.length - d.core.off) =
      d.core.chunk.drop d.core.off := List.take_of_length_le (by simp)
  rw [hbs]
  show DInv P (obsStep o (.imp cStreamWrite [natV d.core.w, bytesV (d.core.chunk.drop d.core.off)] n)) _
  have hw32 := hl.2.1
  have eo : ({ o with wp := some ([], []) } : Obs) = o := by
    rcases o with ⟨os, out, ok, wp, rs, inp, args⟩; simp only at hwp; rw [hwp]
  cases hkn : kont n with
  | none =>
    rw [contWith_none hkn]
    refine dinv_trapped (by rw [obsStep_ok_imp]; exact hok) ?_
    have hn : ∀ pv, n = some [pv] → natOf pv = none := by
      intro pv e
      subst e
      rw [← hk'] at hkn
      dsimp only at hkn
      cases hc : natOf pv with
      | none => rfl
      | some c => simp [hc] at hkn
    have hout : (obsStep o (.imp cStreamWrite [natV d.core.w, bytesV (d.core.chunk.drop d.core.off)]
        n)).out = o.out := by
      simp only [obsStep, os_write_other _ _ _ hn, wbytes, List.filterMap_nil, List.append_nil]
    have hpre := hl.prefOk
    unfold PrefOk at hpre ⊢
    have ht : tgt P (obsStep o (.imp cStreamWrite [natV d.core.w, bytesV (d.core.chunk.drop d.core.off)]
        n)) = tgt P o := by
      simp only [tgt, obsStep, inStep_quiet (show cStreamWrite ≠ stdinRead3 by decide) (by decide)
        (by decide), List.append_nil, argsStep_other (show cStreamWrite ≠ getArgs3 by decide)]
    rw [ht, hout]; exact hpre
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i pv
      cases hc : natOf pv with
      | none => simp only [hc] at hkn; cases hkn
      | some code =>
        simp only [hc, Option.map_some, Option.some.injEq] at hkn
        subst hkn
        rw [obsStep_write hw32 _ pv hc, os_write _ _ pv hw32]
        simp only [hc, Option.bind_some]
        have ht : ∀ o' : Obs, o'.inp = o.inp → o'.args = o.args → tgt P o' = tgt P o := by
          intro o' h1 h2
          simp only [tgt, h1, h2]
        cases hcp : copyOf code with
        | none =>
          have hnb : code ≠ blocked := fun e => by rw [e] at hcp; simp [copyOf] at hcp
          simp only [hnb, ite_false, wbytes, List.filterMap_nil, List.append_nil, hwp,
            Option.bind_some]
          have := failWrite_inv (o := o) hl hwp hpend hm hok hr
          rw [eo]
          simpa only [dresume, afterCall, hpc, afterWrite, hcp] using this
        | some x =>
          rcases x with _ | ⟨res, k⟩
          · have hb : code = blocked := copyOf_blocked.1 hcp
            subst hb
            refine dinv_run hm hok hr ?_
            simp only [PcInv, dresume, afterCall, hpc, afterWrite, hcp, ite_true, wbytes,
              List.filterMap_nil, List.append_nil, hwp, Option.bind_some]
            refine ⟨⟨hl.congr rfl rfl (ht _ rfl rfl) rfl, hlt, rfl, ?_⟩, hpend⟩
            simp
          · have hnb : code ≠ blocked := fun e => by
              rw [e, copyOf_blocked.2 rfl] at hcp; cases hcp
            simp only [hnb, ite_false, hwp, Option.bind_some]
            cases res with
            | completed =>
              refine dinv_run hm hok hr ?_
              simp only [dresume, afterCall, hpc, afterWrite, hcp]
              refine advance_inv hl ?_ rfl (ht _ rfl rfl) rfl rfl hpend
              simp only [hl.1, List.mem_singleton, ite_true, wbytes_map]
            | dropped =>
              have := failWrite_inv (o := o) hl hwp hpend hm hok hr
              dsimp only
              simp only [wbytes, List.filterMap_nil, List.append_nil]
              rw [eo]
              simpa only [dresume, afterCall, hpc, afterWrite, hcp, wbytes, List.filterMap_nil,
                List.append_nil] using this
            | cancelled =>
              have := failWrite_inv (o := o) hl hwp hpend hm hok hr
              dsimp only
              simp only [wbytes, List.filterMap_nil, List.append_nil]
              rw [eo]
              simpa only [dresume, afterCall, hpc, afterWrite, hcp, wbytes, List.filterMap_nil,
                List.append_nil] using this
    · cases hkn

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
