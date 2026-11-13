module

public import Silmaril.Proofs.Wasi.Examples.Handles

/-!
# The filesystem example: descriptors are used only while live, for every host

`writeFile_inv`: the invariant of `writeFile` against `fsHandles` (no assumption on the host).
The preopened directory is live from the answer of `get-directories` to `open-at`, the opened
file from the answer of `open-at` to its drop. Answers only allocate (`fsHEv_imp_allocs`), so
they never break the protocol and keep every live descriptor.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Examples

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol HEv handleProto handleStep Role)

/-- A preopen entry allocates its descriptor. -/
theorem preopenFd_alloc {v : Val} {e : HEv (BitVec 32)} (h : preopenFd v = some e) :
    ∃ d, e = .alloc d := by
  unfold preopenFd at h
  split at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

/-- **Answers only allocate.** -/
theorem fsHEv_imp_allocs (f : FnName) (a : List Val) (n : Option (List Val)) :
    ∀ e ∈ fsHEv (.imp f a n), ∃ d, e = .alloc d := by
  intro e he
  unfold fsHEv at he
  split at he <;> (try split_ifs at he) <;>
    first
    | exact absurd he List.not_mem_nil
    | exact ⟨_, List.mem_singleton.1 he⟩
    | exact preopenFd_alloc (List.mem_filterMap.1 he).choose_spec.2
    | simp_all

/-- The answer of `get-directories` names a directory, or `writeFile` gives up. -/
theorem wfK1_cases (n : Option (List Val)) :
    (∃ d nm rest, n = some [.record (.record [.u32 d, nm] :: rest)]) ∨
      wfK1 n = .pure (some [errV none]) := by
  unfold wfK1
  split
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr rfl

/-- The answer of `open-at` is a descriptor, or `writeFile` gives up. -/
theorem wfK2_cases (n : Option (List Val)) :
    (∃ f, n = some [.variant 0 (some (.u32 f))]) ∨ wfK2 n = .pure (some [errV none]) := by
  unfold wfK2
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr rfl

/-- One step of `fsHandles` on an answer. -/
theorem fs_answer (q : Option (List (BitVec 32))) (f : FnName) (a : List Val)
    (n : Option (List Val)) :
    ∃ q', fsHandles.step q (.imp f a n) = some q' ∧ ∀ x, Has x q → Has x q' :=
  run_allocs (fsHEv_imp_allocs f a n) q

/-- One step of `fsHandles` on a use of a live descriptor. -/
theorem fs_use {q : Option (List (BitVec 32))} {d : BitVec 32} {e : WEv} (hd : Has d q)
    (he : fsHEv e = [.use d]) : fsHandles.step q e = some q := by
  rw [fsHandles_step, he]
  show (handleStep .client q (.use d)).bind _ = _
  rw [use_step hd]
  rfl

/-- The control state of `writeFile` and the descriptor state. -/
def WfInv (c : CSt fsWorld.imports fsWorld.exports) (_ : Unit)
    (qG : Option (List (BitVec 32))) : Prop :=
  (c = .idle ∨ (∃ q, c = .run q wfProg) ∨ (∃ q, c = .wait q dirsOp wfK1) ∨
    (∃ q r, c = .run q (.pure r)) ∨ (∃ q f, c = .wait q (fdropOp f) wfK4)) ∨
  (∃ d, Has d qG ∧ ((∃ q, c = .run q (.call (openOp d) wfK2)) ∨
    (∃ q, c = .wait q (openOp d) wfK2))) ∨
  (∃ f, Has f qG ∧ ((∃ q, c = .run q (.call (fwriteOp f) (wfK3 f))) ∨
    (∃ q, c = .wait q (fwriteOp f) (wfK3 f)) ∨ (∃ q, c = .run q (.call (fdropOp f) wfK4))))

/-- The conclusion of one step of `writeFile`. -/
abbrev WfStep (o : Move (nsig fsWorld.imports) (nsig fsWorld.exports))
    (c' : CSt fsWorld.imports fsWorld.exports) (qG : Option (List (BitVec 32))) : Prop :=
  ∃ qG', fsHandles.step qG (wev o) = some qG' ∧ WfInv c' () qG'

theorem wf_idle {o c' qG} (hc : CStep writeFile .idle o c') : WfStep o c' qG := by
  obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
  exact ⟨qG, rfl, .inl (.inr (.inl ⟨q, rfl⟩))⟩

theorem wf_start {q o c' qG} (hc : CStep writeFile (.run q wfProg) o c') : WfStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := dirsOp) (k := wfK1) hc
  exact ⟨qG, rfl, .inl (.inr (.inr (.inl ⟨q, rfl⟩)))⟩

/-- The descriptors of `get-directories`. -/
theorem dirs_hev (d : BitVec 32) (nm : Val) (rest : List Val) :
    fsHEv (.imp getDirs [] (some [.record (.record [.u32 d, nm] :: rest)])) =
      .alloc d :: rest.filterMap preopenFd :=
  ite_eq_left rfl

theorem wf_dirs {q o c' qG} (hc : CStep writeFile (.wait q dirsOp wfK1) o c') :
    WfStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  rcases wfK1_cases n with ⟨d, nm, rest, rfl⟩ | hk
  · obtain ⟨q₁, h₁, hd₁, -⟩ := alloc_step qG d
    have hl : ∀ e ∈ rest.filterMap preopenFd, ∃ d, e = .alloc d :=
      fun e he => preopenFd_alloc (List.mem_filterMap.1 he).choose_spec.2
    obtain ⟨q₂, h₂, hk₂⟩ := run_allocs hl q₁
    have hstep : fsHandles.step qG (.imp getDirs [] (some [.record (.record [.u32 d, nm] :: rest)]))
        = some q₂ := by
      rw [fsHandles_step, dirs_hev]
      show (handleStep .client qG (.alloc d)).bind _ = _
      rw [h₁]
      exact h₂
    exact ⟨q₂, hstep, .inr (.inl ⟨d, hk₂ d hd₁, .inl ⟨q, rfl⟩⟩)⟩
  · obtain ⟨q', hq', -⟩ := fs_answer qG getDirs [] n
    exact ⟨q', hq', .inl (.inr (.inr (.inr (.inl ⟨q, _, by rw [hk]⟩))))⟩

theorem wf_open {q d o c' qG} (hd : Has d qG)
    (hc : CStep writeFile (.run q (.call (openOp d) wfK2)) o c') : WfStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨qG, fs_use hd (ite_eq_left (.inl rfl)), .inr (.inl ⟨d, hd, .inr ⟨q, rfl⟩⟩)⟩

/-- The descriptor of `open-at`. -/
theorem open_hev (a : List Val) (f : BitVec 32) :
    fsHEv (.imp openAt a (some [.variant 0 (some (.u32 f))])) = [.alloc f] :=
  ite_eq_left rfl

theorem wf_opened {q d o c' qG} (hc : CStep writeFile (.wait q (openOp d) wfK2) o c') :
    WfStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  rcases wfK2_cases n with ⟨f, rfl⟩ | hk
  · obtain ⟨q₁, h₁, hf₁, -⟩ := alloc_step qG f
    have hstep : fsHandles.step qG (.imp openAt [.u32 d, strV "out.txt"]
        (some [.variant 0 (some (.u32 f))])) = some q₁ := by
      rw [fsHandles_step, open_hev]
      show (handleStep .client qG (.alloc f)).bind _ = _
      rw [h₁]
      rfl
    exact ⟨q₁, hstep, .inr (.inr ⟨f, hf₁, .inl ⟨q, rfl⟩⟩)⟩
  · obtain ⟨q', hq', -⟩ := fs_answer qG openAt [.u32 d, strV "out.txt"] n
    exact ⟨q', hq', .inl (.inr (.inr (.inr (.inl ⟨q, _, by rw [hk]⟩))))⟩

theorem wf_write {q f o c' qG} (hf : Has f qG)
    (hc : CStep writeFile (.run q (.call (fwriteOp f) (wfK3 f))) o c') : WfStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  exact ⟨qG, fs_use hf (ite_eq_left (.inr (.inl rfl))), .inr (.inr ⟨f, hf, .inr (.inl ⟨q, rfl⟩)⟩)⟩

theorem wf_written {q f o c' qG} (hf : Has f qG)
    (hc : CStep writeFile (.wait q (fwriteOp f) (wfK3 f)) o c') : WfStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  obtain ⟨q', hq', hk⟩ := fs_answer qG fdWrite [.u32 f, bytesV hiBytes, .u64 0] n
  exact ⟨q', hq', .inr (.inr ⟨f, hk f hf, .inr (.inr ⟨q, rfl⟩)⟩)⟩

/-- The drop of a descriptor. -/
theorem fdrop_hev (f : BitVec 32) :
    fsHEv (wev (X := fsWorld.exports) (.inl (.ask (fdropOp f)))) = [.free f] := by
  show (if fdDrop = openAt ∨ fdDrop = fdWrite ∨ fdDrop = fdRead then [HEv.use f]
    else if fdDrop = fdDrop then [.free f] else []) = _
  rw [ite_eq_right (by decide), ite_eq_left rfl]

theorem wf_drop {q f o c' qG} (hf : Has f qG)
    (hc : CStep writeFile (.run q (.call (fdropOp f) wfK4)) o c') : WfStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.call_inv
  obtain ⟨q', hq'⟩ := free_step hf
  have hstep : fsHandles.step qG (wev (X := fsWorld.exports) (.inl (.ask (fdropOp f)))) =
      some q' := by
    rw [fsHandles_step, fdrop_hev]
    show (handleStep .client qG (.free f)).bind _ = _
    rw [hq']
    rfl
  exact ⟨q', hstep, .inl (.inr (.inr (.inr (.inr ⟨q, f, rfl⟩))))⟩

theorem wf_dropped {q f o c' qG} (hc : CStep writeFile (.wait q (fdropOp f) wfK4) o c') :
    WfStep o c' qG := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  obtain ⟨q', hq', -⟩ := fs_answer qG fdDrop [.u32 f] n
  exact ⟨q', hq', .inl (.inr (.inr (.inr (.inl ⟨q, _, rfl⟩))))⟩

theorem wf_ret {q r o c' qG} (hc : CStep writeFile (.run q (.pure r)) o c') : WfStep o c' qG := by
  obtain ⟨rfl, rfl⟩ := hc.pure_inv
  exact ⟨qG, rfl, .inl (.inl rfl)⟩

/-- **The invariant of `writeFile`.** -/
theorem writeFile_inv : Inv writeFile topP fsHandles WfInv where
  init := .inl (.inl rfl)
  step := fun hc hJ _ => by
    rcases hJ with (rfl | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, r, rfl⟩ | ⟨q, f, rfl⟩) |
      ⟨d, hd, ⟨q, rfl⟩ | ⟨q, rfl⟩⟩ | ⟨f, hf, ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩⟩
    · exact wf_idle hc
    · exact wf_start hc
    · exact wf_dirs hc
    · exact wf_ret hc
    · exact wf_dropped hc
    · exact wf_open hd hc
    · exact wf_opened hc
    · exact wf_write hf hc
    · exact wf_written hf hc
    · exact wf_drop hf hc

end Silmaril.Wasi.Examples
