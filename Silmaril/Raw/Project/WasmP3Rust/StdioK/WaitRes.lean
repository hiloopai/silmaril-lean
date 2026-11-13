module

public import Silmaril.Raw.Project.WasmP3Rust.StdioK.Wait

/-!
# `cat` and `echo` under `DenX.den`: the driver waits

`resume_waitR`, `resume_waitW`, `resume_waitF`: whatever `waitable-set.wait` answers (within
the wait discipline), the callback re-entered with the event keeps the invariant.
-/

@[expose] public section

namespace Silmaril.Raw.Project.WasmP3Rust.StdioK

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.DenX Silmaril.Project.WasmP3Rust.StdioK
open Silmaril.Project.WasmP3Rust.Den (Spaces)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

variable {P : Plan} {S : Spaces}

/-! ## Events -/

theorem evOf_some {n : Option (List Val)} {c i q : Nat} {v : Option Val}
    (h : evOf n = some (c, i, q, v)) :
    (∃ cv iv pv, n = some [cv, iv, pv] ∧ natOf cv = some c ∧ natOf iv = some i ∧
      natOf pv = some q ∧ v = none) ∨
    (∃ cv iv pv x, n = some [cv, iv, pv, x] ∧ natOf cv = some c ∧ natOf iv = some i ∧
      natOf pv = some q ∧ v = some x) := by
  unfold evOf at h
  split at h
  · rename_i cv iv pv
    split at h
    · rename_i c' i' q' hc hi hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact .inl ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩
    · cases h
  · rename_i cv iv pv x
    split at h
    · rename_i c' i' q' hc hi hq
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact .inr ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
    · cases h
  · cases h

theorem onEvent_stay {c : SConf} {code i q : Nat}
    (h : (c.pc = .waitW ∧ code ≠ 3) ∨ (c.pc = .waitR ∧ code ≠ 2) ∨
      (∃ b, c.pc = .waitF b ∧ ¬ (code = 4 ∧ i = c.fut b))) :
    onEvent P c [code, i, q] = c := by
  rcases h with ⟨hpc, h3⟩ | ⟨hpc, h2⟩ | ⟨b, hpc, h4⟩
  · unfold onEvent; split <;> simp_all
  · unfold onEvent; split <;> simp_all
  · unfold onEvent
    split
    · simp_all
    · simp_all
    · rename_i b' i' p' h₁ h₂
      simp only [List.cons.injEq] at h₂
      obtain ⟨rfl, rfl, rfl, -⟩ := h₂
      rw [hpc] at h₁
      cases h₁
      simp only [true_and] at h4
      simp only [h4, ite_false]
    · rfl

theorem onEvent_write {c : SConf} (hpc : c.pc = .waitW) (q : Nat) :
    onEvent P c [3, c.w, q] = match copyOf q with
      | some (some (.completed, k)) => advance P c k
      | _ => failWrite P c := by
  unfold onEvent; rw [hpc]; simp only [↓reduceIte]
  generalize copyOf q = x
  rcases x with _ | _ | ⟨_ | _ | _, k⟩ <;> rfl

theorem onEvent_read {c : SConf} (hpc : c.pc = .waitR) (q : Nat) :
    onEvent P c [2, c.rin, q] = match copyOf q with
      | some (some (res, k)) => gotChunk P c res k
      | _ => { c with pc := .ret 1 } := by
  unfold onEvent; rw [hpc]; simp only [↓reduceIte]
  generalize copyOf q = x
  rcases x with _ | _ | ⟨_ | _ | _, k⟩ <;> rfl

theorem onEvent_fut {c : SConf} {b : Bool} (hpc : c.pc = .waitF b) (q : Nat) :
    onEvent P c [4, c.fut b, q] = match copyOf q with
      | some (some (.completed, _)) => gotFuture c b c.res
      | _ => gotFuture c b 1 := by
  unfold onEvent; rw [hpc]; simp only [↓reduceIte]
  generalize copyOf q = x
  rcases x with _ | _ | ⟨_ | _ | _, k⟩ <;> rfl

theorem dinv_back {o : Obs} {d : DConf (stdioK P)} (c : SConf) (hok : o.ok = false)
    (hr : d.result = none) (h : PcInv P o { d with core := c }) :
    DInv P o { d with core := c, mode := .run } :=
  ⟨hok, .inl ⟨hr, h⟩⟩

/-! ## `waitW` -/

theorem resume_waitW {o : Obs} {d : DConf (stdioK P)} {s : Nat} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitW) (hp : Blocked P o d.core)
    (hpend : d.pend = []) (n : Option (List Val))
    (hacc : (obsStep o (.imp cWait [natV s] n)).wp.isSome) :
    DInv P (obsStep o (.imp cWait [natV s] n)) (afterWait P.cb d n) := by
  obtain ⟨hl, hlt, hwp, hfind⟩ := hp
  have hwt : waiting d.core.pc = true := by rw [hpc]; rfl
  cases hev : evOf n with
  | none =>
    rw [afterWait_none hev]
    obtain ⟨h1, h2, h3⟩ := obsStep_wait_evNone o [natV s] hev
    exact dinv_trapped (by rw [obsStep_ok_imp]; exact hok) (prefOk_congr h1 h2 h3 hl.prefOk)
  | some e =>
    obtain ⟨c, i, q, v⟩ := e
    have hdl : deliver d c i v = some d := deliver_nofind (by rw [hpend]; rfl)
    rw [afterWait_some hev hdl, reenter_eq _ hwt]
    by_cases h3 : c = 3
    · subst h3
      rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
        ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
      · by_cases hiw : i = d.core.w
        · subst hiw
          rw [obsStep_wait_write _ hwp hc hi hfind (by rw [hl.1]; simp), hq, Option.bind_some,
            onEvent_write hpc]
          have hl' : Live P { o with wp := some ([], []) } d.core := hl.congr rfl rfl rfl rfl
          cases hcp : copyOf q with
          | none =>
            simp only [wout, List.append_nil]
            exact failWrite_inv (d := { d with mode := .run }) hl' rfl hpend rfl hok hr
          | some x =>
            rcases x with _ | ⟨res, k⟩
            · simp only [wout, List.append_nil]
              exact failWrite_inv (d := { d with mode := .run }) hl' rfl hpend rfl hok hr
            · cases res with
              | completed =>
                refine dinv_back _ hok hr ?_
                exact advance_inv hl (by simp only [wout]) rfl rfl rfl rfl hpend
              | dropped =>
                simp only [wout, List.append_nil]
                exact failWrite_inv (d := { d with mode := .run }) hl' rfl hpend rfl hok hr
              | cancelled =>
                simp only [wout, List.append_nil]
                exact failWrite_inv (d := { d with mode := .run }) hl' rfl hpend rfl hok hr
        · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
            (fun j hj _ => by rw [hi] at hj; cases hj; simpa using hiw)
          rw [e] at hacc; cases hacc
      · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
          (fun _ _ h => by cases h)
        rw [e] at hacc; cases hacc
    · by_cases h2 : c = evStreamRead
      · subst h2
        rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
          ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
        · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
            (fun _ _ _ h => by cases h)
          rw [e] at hacc; cases hacc
        · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
            (fun _ _ _ _ => by simp)
          rw [e] at hacc; cases hacc
      · have hq : obsStep o (.imp cWait [natV s] n) = o := by
          refine obsStep_wait_quiet o _ n fun cv iv pv rest e => ?_
          rcases evOf_some hev with ⟨cv', iv', pv', e', hc, -⟩ | ⟨cv', iv', pv', x, e', hc, -⟩ <;>
            (rw [e'] at e; simp only [Option.some.injEq, List.cons.injEq] at e;
             obtain ⟨rfl, -⟩ := e; rw [hc]; exact ⟨fun h => h3 (Option.some.inj h),
               fun h => h2 (Option.some.inj h)⟩)
        rw [hq, onEvent_stay (.inl ⟨hpc, h3⟩)]
        refine dinv_back _ hok hr ?_
        simp only [PcInv, hpc]
        exact ⟨⟨hl, hlt, hwp, hfind⟩, hpend⟩

/-! ## `waitR` -/

theorem resume_waitR {o : Obs} {d : DConf (stdioK P)} {s : Nat} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitR) (hp : PcInv P o d) (n : Option (List Val))
    (hacc : (obsStep o (.imp cWait [natV s] n)).wp.isSome) :
    DInv P (obsStep o (.imp cWait [natV s] n)) (afterWait P.cb d n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hl, hoff, hwp, hpend, hk⟩ := hp
  have hsrc := hl.2.2.2
  simp only [Src, hk] at hsrc
  obtain ⟨hrs, hr32⟩ := hsrc
  have hwt : waiting d.core.pc = true := by rw [hpc]; rfl
  cases hev : evOf n with
  | none =>
    rw [afterWait_none hev]
    obtain ⟨h1, h2, h3⟩ := obsStep_wait_evNone o [natV s] hev
    exact dinv_trapped (by rw [obsStep_ok_imp]; exact hok) (prefOk_congr h1 h2 h3 hl.prefOk)
  | some e =>
    obtain ⟨c, i, q, v⟩ := e
    by_cases h3 : c = 3
    · subst h3
      rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
        ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
      · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
          (fun _ _ _ => by simp)
        rw [e] at hacc; cases hacc
      · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
          (fun _ _ h => by cases h)
        rw [e] at hacc; cases hacc
    · by_cases h2 : c = evStreamRead
      · subst h2
        rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
          ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
        · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
            (fun _ _ _ h => by cases h)
          rw [e] at hacc; cases hacc
        · by_cases hir : i = d.core.rin
          · subst hir
            rw [obsStep_wait_read _ hwp hrs hc hi hq, afterWait_some hev (deliver_read hpend x)]
            have hst : store d.core 0 (bytesOf x) = { d.core with buf := bytesOf x } := by
              simp [store]
            rw [hst, reenter_eq (d := { d with pend := [], core := { d.core with buf := bytesOf x } })
              _ hwt]
            have ho := onEvent_read (P := P) (c := { d.core with buf := bytesOf x }) hpc q
            dsimp only at ho ⊢
            rw [show evStreamRead = 2 from rfl, ho]
            cases hcp : copyOf q with
            | none =>
              have hcc : copyCount q = none := copyCount_none fun r k e => by rw [hcp] at e; cases e
              simp only [hcc, Option.map_none, Option.getD_none, List.append_nil]
              refine dinv_run rfl hok hr ?_
              simp only [PcInv]
              exact ⟨hl.congr rfl rfl rfl rfl, fun h => absurd h (by decide), trivial,
                fun _ h => absurd h List.not_mem_nil⟩
            | some y =>
              rcases y with _ | ⟨res, k⟩
              · have hcc : copyCount q = none :=
                  copyCount_none fun r k e => by rw [hcp] at e; cases e
                simp only [hcc, Option.map_none, Option.getD_none, List.append_nil]
                refine dinv_run rfl hok hr ?_
                simp only [PcInv]
                exact ⟨hl.congr rfl rfl rfl rfl, fun h => absurd h (by decide), trivial,
                  fun _ h => absurd h List.not_mem_nil⟩
              · simp only [copyCount_of hcp, Option.map_some, Option.getD_some]
                refine dinv_run rfl hok hr ?_
                exact gotChunk_inv (o := o) (c := { d.core with buf := bytesOf x })
                  (d := { d with pend := [], mode := .run }) hk hl hoff rfl rfl rfl rfl rfl rfl
          · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
              (fun j y hj _ => by rw [hi] at hj; cases hj; simpa using hir)
            rw [e] at hacc; cases hacc
      · have hq : obsStep o (.imp cWait [natV s] n) = o := by
          refine obsStep_wait_quiet o _ n fun cv iv pv rest e => ?_
          rcases evOf_some hev with ⟨cv', iv', pv', e', hc, -⟩ | ⟨cv', iv', pv', x, e', hc, -⟩ <;>
            (rw [e'] at e; simp only [Option.some.injEq, List.cons.injEq] at e;
             obtain ⟨rfl, -⟩ := e; rw [hc]; exact ⟨fun h => h3 (Option.some.inj h),
               fun h => h2 (Option.some.inj h)⟩)
        have hdl : deliver d c i v = some d := deliver_nofind (by
          rw [hpend]; simp only [List.find?_cons, List.find?_nil]
          simp [Ne.symm h2])
        rw [hq, afterWait_some hev hdl, reenter_eq _ hwt, onEvent_stay (.inr (.inl ⟨hpc, h2⟩))]
        refine dinv_back _ hok hr ?_
        simp only [PcInv, hpc]
        exact ⟨hl, hoff, hwp, hpend, hk⟩

/-! ## `waitF` -/

theorem deliver_some (d : DConf (stdioK P)) (c i : Nat) (v : Option Val) :
    ∃ d', deliver d c i v = some d' := by
  unfold deliver
  split
  · split
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem Done.congr {o : Obs} {c c' : SConf} (h : Done P o c) (hw : c'.w = c.w)
    (hch : c'.chunk = c.chunk) (hoff : c'.off = c.off) (hrin : c'.rin = c.rin) : Done P o c' := by
  obtain ⟨⟨h1, h2, ⟨⟨m, hm, he⟩, hle⟩, h4⟩, h5, h6⟩ := h
  refine ⟨⟨hw ▸ h1, hw ▸ h2, ⟨⟨m, hm, by rw [hch, hoff]; exact he⟩, by rw [hch, hoff]; exact hle⟩,
    ?_⟩, by rw [hch, hoff]; exact h5, h6⟩
  unfold Src at h4 ⊢; rw [hrin]; exact h4

theorem resume_waitF {o : Obs} {d : DConf (stdioK P)} {s : Nat} {b : Bool} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitF b) (hp : PcInv P o d) (n : Option (List Val))
    (hacc : (obsStep o (.imp cWait [natV s] n)).wp.isSome) :
    DInv P (obsStep o (.imp cWait [natV s] n)) (afterWait P.cb d n) := by
  simp only [PcInv, hpc] at hp
  obtain ⟨hd, hpf⟩ := hp
  have hwp := hd.2.2
  cases hev : evOf n with
  | none =>
    rw [afterWait_none hev]
    obtain ⟨h1, h2, h3⟩ := obsStep_wait_evNone o [natV s] hev
    exact dinv_trapped (by rw [obsStep_ok_imp]; exact hok) (prefOk_congr h1 h2 h3 hd.1.prefOk)
  | some e =>
    obtain ⟨c, i, q, v⟩ := e
    by_cases h3 : c = 3
    · subst h3
      rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
        ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
      · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
          (fun _ _ _ => by simp)
        rw [e] at hacc; cases hacc
      · have e := obsStep_wait_refused3 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
          (fun _ _ h => by cases h)
        rw [e] at hacc; cases hacc
    · by_cases h2 : c = evStreamRead
      · subst h2
        rcases evOf_some hev with ⟨cv, iv, pv, rfl, hc, hi, hq, rfl⟩ |
          ⟨cv, iv, pv, x, rfl, hc, hi, hq, rfl⟩
        · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := []) hwp hc
            (fun _ _ _ h => by cases h)
          rw [e] at hacc; cases hacc
        · have e := obsStep_wait_refused2 [natV s] (iv := iv) (pv := pv) (rest := [x]) hwp hc
            (fun _ _ _ _ => by simp)
          rw [e] at hacc; cases hacc
      · have hq : obsStep o (.imp cWait [natV s] n) = o := by
          refine obsStep_wait_quiet o _ n fun cv iv pv rest e => ?_
          rcases evOf_some hev with ⟨cv', iv', pv', e', hc, -⟩ | ⟨cv', iv', pv', x, e', hc, -⟩ <;>
            (rw [e'] at e; simp only [Option.some.injEq, List.cons.injEq] at e;
             obtain ⟨rfl, -⟩ := e; rw [hc]; exact ⟨fun h => h3 (Option.some.inj h),
               fun h => h2 (Option.some.inj h)⟩)
        obtain ⟨d', hdl⟩ := deliver_some d c i v
        obtain ⟨hm', hr', hpf', hpc', hoff', hch', hw', hrin', -, hf', hfin'⟩ := deliver_fut hpf hdl
        have hd' : Done P o d'.core := hd.congr hw' hch' hoff' hrin'
        have hwt : waiting d'.core.pc = true := by rw [hpc', hpc]; rfl
        rw [hq, afterWait_some hev hdl, reenter_eq _ hwt]
        have hpc'' : d'.core.pc = .waitF b := hpc'.trans hpc
        refine dinv_back _ hok (hr'.trans hr) ?_
        by_cases hfe : c = 4 ∧ i = d'.core.fut b
        · obtain ⟨rfl, rfl⟩ := hfe
          rw [onEvent_fut hpc'']
          split <;> exact gotFuture_inv (d := d') hd' hpf'
        · rw [onEvent_stay (.inr (.inr ⟨b, hpc'', hfe⟩))]
          simp only [PcInv, hpc'']
          exact ⟨hd', hpf'⟩

end Silmaril.Raw.Project.WasmP3Rust.StdioK

end
