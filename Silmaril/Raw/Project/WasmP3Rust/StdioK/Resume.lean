module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Args

/-!
# `cat` and `echo` under `DenX.den`: answers keep the invariant (set-up calls)

One lemma per program point that calls the world before the loop (`src`, `new`, `wvs`,
`wsNew`), and for the quiet calls (`join`, `stream.drop-writable`, `future.read`): whatever the
host answers, the next configuration satisfies `DInv` for the observations extended by the
answer.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

/-! ## Building the invariant -/

theorem dinv_trapped {o : Obs} {d : DConf (stdioK P)} (hok : o.ok = false) (h : PrefOk P o) :
    DInv P o d.trapped := ⟨hok, h⟩

theorem dinv_run {o : Obs} {d : DConf (stdioK P)} (hm : d.mode = .run) (hok : o.ok = false)
    (hr : d.result = none) (h : PcInv P o d) : DInv P o d := by
  refine ⟨hok, ?_⟩
  simp only [hm]
  exact .inl ⟨hr, h⟩

theorem dinv_run_trapped {o : Obs} {d : DConf (stdioK P)} (hm : d.mode = .run)
    (hok : o.ok = false) (hc : d.core.pc = .trapped) (h : PrefOk P o) : DInv P o d := by
  refine ⟨hok, ?_⟩
  simp only [hm]
  exact .inr (.inr ⟨hc, h⟩)

/-- The continuation of a forwarded built-in. -/
theorem contWith_none {d : DConf (stdioK P)} {kont : Option (List Val) → Option (DConf (stdioK P))}
    {n : Option (List Val)} (h : kont n = none) : contWith d kont n = d.trapped := by
  simp only [contWith, h]

theorem contWith_some {d d' : DConf (stdioK P)}
    {kont : Option (List Val) → Option (DConf (stdioK P))} {n : Option (List Val)}
    (h : kont n = some d') : contWith d kont n = d' := by
  simp only [contWith, h]

theorem dstore (d : DConf (stdioK P)) (p : Nat) (bs : List (BitVec 8)) :
    d.store p bs = some { d with core := store d.core p bs } := rfl

theorem dresume (d : DConf (stdioK P)) (vs : List Nat) :
    d.resume vs = { d with core := afterCall P d.core vs } := rfl

/-- The call of a program point, from `callOf`. -/
theorem call_eq {c : SConf} {k' k0 : Nat} {args a0 : List Nat} (hc : callOf P c = some (k0, a0))
    (hco : callOf P c = some (k', args)) : k' = k0 ∧ args = a0 := by
  rw [hc] at hco; simpa only [Option.some.injEq, Prod.mk.injEq] using hco.symm

/-! ## The OS image and the other observations on the set-up events -/

theorem os_out_nil {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cWait) (q : OsSt) (a r) :
    (osStep3 0 q (.imp f a r)).2 = [] := by
  unfold osStep3
  dsimp only
  simp only [h1, h2, ite_false]
  split_ifs <;> (repeat' split) <;> rfl

theorem obsStep_noemit {f : FnName} (h1 : f ≠ cStreamWrite) (h2 : f ≠ cWait)
    (h3 : f ≠ cStreamRead) (h4 : f ≠ stdinRead3) (h5 : f ≠ getArgs3) (o : Obs) (a : List Val)
    (r : Option (List Val)) :
    obsStep o (.imp f a r) = { o with os := (osStep3 0 o.os (.imp f a r)).1 } := by
  rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
  simp only [obsStep, os_out_nil h1 h2, wbytes, List.filterMap_nil, List.append_nil, okEv,
    Bool.or_false, waitStepX_quiet h1 h3 h2, inStep_quiet h4 h3 h2, argsStep_other h5]
  cases wp <;> rfl

theorem os_new (q : OsSt) {rv wv : Val} {r w : Nat} (hr : natOf rv = some r)
    (hw : natOf wv = some w) :
    osStep3 0 q (.imp cStreamNew [] (some [rv, wv])) =
      ({ q with pairs := (r, w) :: q.pairs }, []) := by
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

/-! ## `src` -/

theorem src_cat {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hk : P.kind = .cat)
    (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .src)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hout, hos, hwp, hrs, hinp, hargs, -, -, hch, hoff, hpend⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.src) (a0 := [retA]) (by simp only [callOf, hpc]) hco
  rw [hw.src, hk] at hf
  simp only [srcB, forward, ite_true, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  show DInv P (obsStep o (.imp stdinRead3 [] n)) _
  have hq : obsStep o (.imp stdinRead3 [] n) =
      { o with rs := (inStep o.rs (.imp stdinRead3 [] n)).1 } := by
    rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
    have h1 : osStep3 0 os (.imp stdinRead3 [] n) = (os, []) := os_quiet (by decide) (by decide)
      (by decide) (by decide) _ _ _
    have h2 : ∀ q, waitStepX q (.imp stdinRead3 [] n) = some q := fun q =>
      waitStepX_quiet (f := stdinRead3) (by decide) (by decide) (by decide) q [] n
    have h3 : (inStep rs (.imp stdinRead3 [] n)).2 = [] := by
      unfold inStep
      simp only [ite_true]
      split <;> (try split) <;> rfl
    simp only [obsStep, h1, h2, h3, wbytes, List.filterMap_nil, List.append_nil, okEv,
      Bool.or_false, argsStep_other (show stdinRead3 ≠ getArgs3 by decide)]
    cases wp <;> rfl
  rw [hq]
  cases hkn : kont n with
  | none => rw [contWith_none hkn]; exact dinv_trapped hok (prefOk_nil hout)
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i a b
      split at hkn
      · rename_i a' b' ha hb
        simp only [dstore, Option.map_some, Option.some.injEq] at hkn
        subst hkn
        have hrs' : (inStep o.rs (.imp stdinRead3 [] (some [.record [a, b]]))).1 = [a'] := by
          unfold inStep
          simp only [ite_true, ha, hrs]
        refine dinv_run hm hok hr ?_
        have hst : store d.core retA (Den.le32 a' ++ Den.le32 b') =
            { d.core with ret := Den.le32 a' ++ Den.le32 b' } := by simp [store, retA]
        simp only [PcInv, dresume, afterCall, hst, hpc, afterSrc, hk, hrs', dec32_take _ _
          (natOf_lt ha), dec32_drop _ _ (natOf_lt hb)]
        refine ⟨hout, hos, hwp, ⟨⟨[], ?_, ?_⟩, ?_⟩, by simpa [Src, hk] using natOf_lt ha,
          hpend, fun _ => ?_⟩
        · simp only [tgt, hk, hinp]
        · simp [hout, hch]
        · simp [hch, hoff]
        · simp [hch, hoff]
      · cases hkn
    · cases hkn

theorem src_echo {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S) (hk : P.kind = .echo)
    (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .src)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hout, hos, hwp, hrs, hinp, hargs, -, hnext, hch, hoff, hpend⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.src) (a0 := [retA]) (by simp only [callOf, hpc]) hco
  rw [hw.src, hk] at hf
  simp only [srcB, forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  show DInv P (obsStep o (.imp getArgs3 [] n)) _
  have hq : obsStep o (.imp getArgs3 [] n) = { o with args := argsOf n } := by
    rcases o with ⟨os, out, ok, wp, rs, inp, args⟩
    have h1 : osStep3 0 os (.imp getArgs3 [] n) = (os, []) := os_quiet (by decide) (by decide)
      (by decide) (by decide) _ _ _
    have h2 : ∀ q, waitStepX q (.imp getArgs3 [] n) = some q := fun q =>
      waitStepX_quiet (f := getArgs3) (by decide) (by decide) (by decide) q [] n
    have h3 : inStep rs (.imp getArgs3 [] n) = (rs, []) :=
      inStep_quiet (by decide) (by decide) (by decide) _ _ _
    simp only [obsStep, h1, h2, h3, wbytes, List.filterMap_nil, List.append_nil, okEv,
      Bool.or_false, argsStep, ite_true]
    cases wp <;> rfl
  rw [hq]
  cases hkn : kont n with
  | none => rw [contWith_none hkn]; exact dinv_trapped hok (prefOk_nil hout)
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i ss hss
      cases hl : lowerArgs (stdioK P) d.core retA ss with
      | none => rw [hl] at hkn; cases hkn
      | some y =>
        rw [hl, Option.map_some, Option.some.injEq] at hkn
        subst hkn
        obtain ⟨hypc, hya⟩ := lowerArgs_spec hl hnext
        refine dinv_run hm hok hr ?_
        simp only [PcInv, afterCall, hypc, hpc, afterSrc, hk, hya]
        refine ⟨hout, hos, hwp, ⟨⟨lineOf ss, ?_, ?_⟩, ?_⟩, by simp [Src, hk], hpend,
          fun h => by cases h⟩
        · simp only [tgt, hk, hss, Option.map_some]
        · simp [hout]
        · simp
    · cases hkn

/-! ## `new`, `wvs` -/

theorem cStreamNew_ne : cStreamNew ≠ cStreamWrite ∧ cStreamNew ≠ cWait ∧ cStreamNew ≠ cStreamRead ∧
    cStreamNew ≠ stdinRead3 ∧ cStreamNew ≠ getArgs3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem stdoutWrite3_ne : stdoutWrite3 ≠ cStreamWrite ∧ stdoutWrite3 ≠ cWait ∧
    stdoutWrite3 ≠ cStreamRead ∧ stdoutWrite3 ≠ stdinRead3 ∧ stdoutWrite3 ≠ getArgs3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem resume_new {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S)
    (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .new)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hout, hos, hwp, hacc, hsrc, hpend, hcat⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.streamNew) (a0 := []) (by simp only [callOf, hpc]) hco
  rw [hw.streamNew] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  show DInv P (obsStep o (.imp cStreamNew [] n)) _
  obtain ⟨h1, h2, h3, h4, h5⟩ := cStreamNew_ne
  rw [obsStep_noemit h1 h2 h3 h4 h5]
  cases hkn : kont n with
  | none => rw [contWith_none hkn]; exact dinv_trapped hok (prefOk_nil hout)
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i rv wv
      split at hkn
      · rename_i r w hrv hwv
        rw [Option.some.injEq] at hkn
        subst hkn
        rw [os_new _ hrv hwv]
        refine dinv_run hm hok hr ?_
        simp only [PcInv, dresume, afterCall, hpc, pack_mod (natOf_lt hrv), pack_div (natOf_lt hrv)]
        refine ⟨hout, by simp [hos], by simp, natOf_lt hrv, natOf_lt hwv, hwp, hacc, hsrc, hpend,
          hcat⟩
      · cases hkn
    · cases hkn

theorem resume_wvs {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S)
    (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .wvs)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hout, hw0, hfind, hr32, hw32, hwp, hacc, hsrc, hpend, hcat⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.wvs) (a0 := [d.core.r]) (by simp only [callOf, hpc]) hco
  rw [hw.wvs] at hf
  simp only [forward, show stdoutWrite3 ≠ stdinRead3 by decide, ite_false, ite_true,
    Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  show DInv P (obsStep o (.imp stdoutWrite3 [natV d.core.r] n)) _
  obtain ⟨h1, h2, h3, h4, h5⟩ := stdoutWrite3_ne
  rw [obsStep_noemit h1 h2 h3 h4 h5, os_wvs]
  simp only [natOf_natV hr32, Option.bind_some, hfind]
  cases hkn : kont n with
  | none => rw [contWith_none hkn]; exact dinv_trapped hok (prefOk_nil hout)
  | some d' =>
    rw [contWith_some hkn]
    rw [← hk'] at hkn
    dsimp only at hkn
    split at hkn
    · rename_i v
      cases hv : natOf v with
      | none => rw [hv] at hkn; cases hkn
      | some fv =>
        rw [hv, Option.map_some, Option.some.injEq] at hkn
        subst hkn
        refine dinv_run hm hok hr ?_
        simp only [PcInv, dresume, afterCall, hpc]
        exact ⟨⟨by simp [hw0], hw32, hacc, hsrc⟩, hwp, hpend, hcat⟩
    · cases hkn

/-! ## Quiet calls -/

theorem resume_quiet {o : Obs} {d : DConf (stdioK P)} {f : FnName} {a : List Val}
    {n : Option (List Val)} {kont : Option (List Val) → Option (DConf (stdioK P))} (hq : Quiet f)
    (hok : o.ok = false) (hpre : PrefOk P o)
    (hk : ∀ d', kont n = some d' → d'.mode = .run ∧ d'.result = none ∧ PcInv P o d') :
    DInv P (obsStep o (.imp f a n)) (contWith d kont n) := by
  rw [obsStep_quiet hq]
  cases hkn : kont n with
  | none => rw [contWith_none hkn]; exact dinv_trapped hok hpre
  | some d' =>
    rw [contWith_some hkn]
    obtain ⟨h1, h2, h3⟩ := hk d' hkn
    exact dinv_run h1 hok h2 h3

/-- After a chunk is out (`off = len`), with nothing blocked. -/
theorem afterChunk_inv {o : Obs} {d : DConf (stdioK P)} {c : SConf} (hl : Live P o c)
    (hoff : c.off = c.chunk.length) (hwp : o.wp = some ([], [])) (hpend : d.pend = []) :
    PcInv P o { d with core := afterChunk P c } := by
  unfold afterChunk
  split
  · rename_i h
    simp only [PcInv]
    exact ⟨⟨hl, hoff, hwp⟩, hpend, h.1⟩
  · simp only [PcInv]
    exact ⟨⟨hl, hoff, hwp⟩, by rw [hpend]; exact fun _ h => absurd h List.not_mem_nil⟩

/-- Start writing a chunk. -/
theorem startChunk_inv {o : Obs} {d : DConf (stdioK P)} {c : SConf} (hl : Live P o c)
    (hwp : o.wp = some ([], [])) (hpend : d.pend = []) :
    PcInv P o { d with core := startChunk P c } := by
  unfold startChunk
  split
  · rename_i h
    simp only [PcInv]
    exact ⟨hl, h, hwp, hpend⟩
  · rename_i h
    exact afterChunk_inv hl (Nat.le_antisymm hl.2.2.1.2 (Nat.not_lt.1 h)) hwp hpend

theorem resume_wsNew {o : Obs} {d : DConf (stdioK P)} (hw : Wiring P S)
    (hm : d.mode = .run) (hok : o.ok = false) (hr : d.result = none) (hpc : d.core.pc = .wsNew)
    (hp : PcInv P o d) {k' : Nat} {args : List Nat} {m : XOp}
    {kont : Option (List Val) → Option (DConf (stdioK P))}
    (hco : callOf P d.core = some (k', args)) (hf : forward (builtinX S k') args d = some (m, kont))
    (n : Option (List Val)) : DInv P (obsStep o (.imp m.1.1 m.2 n)) (contWith d kont n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hl, hwp, hpend, hcat⟩ := hp
  obtain ⟨rfl, rfl⟩ := call_eq (k0 := P.wsNew) (a0 := []) (by simp only [callOf, hpc]) hco
  rw [hw.wsNew] at hf
  simp only [forward, Option.some.injEq, Prod.mk.injEq] at hf
  obtain ⟨rfl, hk'⟩ := hf
  refine resume_quiet quiet_wsNew hok hl.prefOk fun d' hkn => ?_
  rw [← hk'] at hkn
  dsimp only at hkn
  split at hkn
  · rename_i sv
    cases hs : natOf sv with
    | none => rw [hs] at hkn; cases hkn
    | some s =>
      rw [hs, Option.map_some, Option.some.injEq] at hkn
      subst hkn
      refine ⟨hm, hr, ?_⟩
      simp only [dresume, afterCall, hpc]
      split
      · rename_i hk
        simp only [PcInv]
        exact ⟨⟨hl, hcat hk, hwp⟩, hpend, hk⟩
      · exact startChunk_inv hl hwp hpend
  · cases hkn

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
