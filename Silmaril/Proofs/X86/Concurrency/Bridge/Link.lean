module

public import Silmaril.X86.Concurrency.Bridge.Defs
public import Silmaril.X86.Atomic9.Converse.Thms
public import Silmaril.X86.Concurrency.Cir.TvCfg.Thms
public import Silmaril.Proofs.X86.Concurrency.Bridge.Step
public import Silmaril.Proofs.X86.Concurrency.Bridge.Defined

/-!
# Calls on the real machine (gap 4): proofs

`Task.callRet` and the soundness of the caller checker `ltv` (header
`Silmaril.X86.Concurrency.Bridge.Thms`). The pieces:

* `call_exec`, `ret_exec`: `Atomic9.exec` of `call rel32` and `ret` is `pushWord`/`popWord`
  (unfolding `Ext.exec`);
* `call_law`, `ret_law`: a successful `Atomic9.step` at a listed `call` or `ret` of a loaded
  image is that execution (the converse of the listing law, `Atomic9.exec_of_step_base`);
* `callRet_holds`: the call and `ret` laws plus `tvCfg_steps` on the callee's slice;
* `ltv_sound`: by induction over the caller run `LRun`, each segment and callee body is a CIR
  run by `tvCfg_real` (re-derived here from `xrun_of_a9run` and `tvCfgDefined_holds`), the
  `call` and `ret` are the glue `push8`/`pop8`, and the runs compose under `seq`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.Link

open Silmaril.X86 (State MState Byte pushWord popWord)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Litmus (SeqStep)
open Silmaril.X86.MemoryModel.Litmus (XAct)
open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.TvCfg
open Silmaril.X86.Concurrency.Bridge
open Silmaril.X86.Concurrency.Cir.Tv (XThread fetchAt)

/-! ## The call and `ret` laws -/

theorem fetchAt_dec {t : XThread} {o : Nat} {i : Atomic9.Instr} {n : Nat}
    (h : fetchAt t o = some (i, n)) :
    o + n ≤ t.code.length ∧ Atomic9.decode ((t.code.drop o).take n) = some (i, n) := by
  unfold fetchAt at h
  split at h
  · split at h
    · cases h; assumption
    · cases h
  · cases h

theorem call_exec {s c : State} {m m' : Memory} {rel : BitVec 32}
    (h : Atomic9.exec (.open9 (.ext8 (.base (.call rel)))) s m 5 = .ok c m') :
    m.writeBytes (s.read .rsp - 8).toNat (encodeWords [s.rip + 5]) = some m' ∧
      c = { s.write .rsp (s.read .rsp - 8) with rip := s.rip + 5 + rel.signExtend 64 } := by
  simp only [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, pushWord] at h
  cases hw : m.writeBytes (s.read .rsp - 8#64).toNat (encodeWords [s.rip + BitVec.ofNat 64 5]) with
  | none => rw [hw] at h; cases h
  | some m2 =>
    rw [hw] at h
    simp only [Option.map_some, Silmaril.X86.Ext.Result.ok.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    exact ⟨rfl, rfl⟩

theorem ret_exec {s c : State} {m m' : Memory} {v : BitVec 64}
    (hr : m.readBytes (s.read .rsp).toNat 8 = some (encodeWords [v]))
    (h : Atomic9.exec (.open9 (.ext8 (.base .ret))) s m 1 = .ok c m') :
    m' = m ∧ c = { s.write .rsp (s.read .rsp + 8) with rip := v } := by
  simp only [Atomic9.exec, Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, popWord] at h
  rw [hr] at h
  simp only [Option.bind_eq_bind, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords,
    Option.pure_def, Silmaril.X86.Ext.Result.ok.injEq] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h2.symm, h1.symm⟩

/-- `C3` is the listed `ret`. -/
theorem decode_ret : Atomic9.decode [0xC3] = some (.open9 (.ext8 (.base .ret)), 1) := by decide

theorem take_one_drop {l : List Byte} {k : Nat} {x : Byte} (h : l[k]? = some x) :
    (l.drop k).take 1 = [x] := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.drop_eq_getElem_cons hk]; rfl

theorem slice_len {t : XThread} {lo n : Nat} (h : lo + n ≤ t.code.length) :
    (slice t lo (lo + n)).code.length = n := by
  simp [slice]; omega

theorem slice_base (t : XThread) (lo hi : Nat) :
    (slice t lo hi).base = t.base + BitVec.ofNat 64 lo := rfl

theorem slice_endRip {t : XThread} {lo n : Nat} (h : lo + n ≤ t.code.length) :
    (slice t lo (lo + n)).endRip = t.base + BitVec.ofNat 64 (lo + n) := by
  rw [Silmaril.X86.Litmus.Thread.endRip, slice_len h, slice_base, BitVec.ofNat_add,
    BitVec.add_assoc]

/-- **The call law**: a successful step at a listed `call rel32` pushes the return address,
lowers `rsp` by 8, keeps every other register and goes to the target. -/
theorem call_law {t : XThread} {o fo : Nat} (hCall : CallAt t o fo) {s s₁ : State}
    {m₁ m₂ : Memory} (hrip : s.rip = t.base + BitVec.ofNat 64 o) (hl1 : Loaded m₁ t.base t.code)
    (hs : Atomic9.step ⟨s, m₁⟩ = some ⟨s₁, m₂⟩) :
    m₁.writeBytes (s.read .rsp - 8).toNat (encodeWords [s.rip + 5]) = some m₂ ∧
      s₁.read .rsp = s.read .rsp - 8 ∧ s₁.rip = t.base + BitVec.ofNat 64 fo ∧
      ∀ r : Silmaril.X86.Reg, r ≠ .rsp → s₁.read r = s.read r := by
  obtain ⟨rel, hf, htgt⟩ := hCall
  obtain ⟨hfit, hdec⟩ := fetchAt_dec hf
  have hx : Atomic9.exec _ s m₁ 5 = .ok s₁ m₂ :=
    Atomic9.exec_of_step_base (m := ⟨s, m₁⟩) (m' := ⟨s₁, m₂⟩) hl1 hrip hfit hdec hs
  obtain ⟨hw, hs1⟩ := call_exec hx
  refine ⟨hw, ?_, ?_, ?_⟩
  · rw [hs1]; show (s.write .rsp _).read .rsp = _; exact State.read_write_same ..
  · rw [← htgt, hs1, hrip, BitVec.ofNat_add]; dsimp only; bv_omega
  · intro r hr; rw [hs1]; simp [State.read, State.write, hr]

/-- **The `ret` law**: a successful step at a listed `ret` whose stack slot holds `w` goes to
`w`, raises `rsp` by 8, keeps every other register and does not change memory. -/
theorem ret_law {t : XThread} {k : Nat} (hC3 : t.code[k]? = some 0xC3) {s₂ s₃ : State}
    {m₃ m₄ : Memory} {w : BitVec 64} (hrip : s₂.rip = t.base + BitVec.ofNat 64 k)
    (hl : Loaded m₃ t.base t.code)
    (hread : m₃.readBytes (s₂.read .rsp).toNat 8 = some (encodeWords [w]))
    (hs : Atomic9.step ⟨s₂, m₃⟩ = some ⟨s₃, m₄⟩) :
    s₃.rip = w ∧ s₃.read .rsp = s₂.read .rsp + 8 ∧ m₄ = m₃ ∧
      ∀ r : Silmaril.X86.Reg, r ≠ .rsp → s₃.read r = s₂.read r := by
  have hk : k < t.code.length := (List.getElem?_eq_some_iff.mp hC3).1
  have hdec : Atomic9.decode ((t.code.drop k).take 1) = some (.open9 (.ext8 (.base .ret)), 1) := by
    rw [take_one_drop hC3]; exact decode_ret
  have hx : Atomic9.exec _ s₂ m₃ 1 = .ok s₃ m₄ :=
    Atomic9.exec_of_step_base (m := ⟨s₂, m₃⟩) (m' := ⟨s₃, m₄⟩) hl hrip (by omega) hdec hs
  obtain ⟨hm, hs3⟩ := ret_exec hread hx
  refine ⟨by rw [hs3], ?_, hm, ?_⟩
  · rw [hs3]; show (s₂.write .rsp _).read .rsp = _; exact State.read_write_same ..
  · intro r hr; rw [hs3]; simp [State.read, State.write, hr]

/-- **`Task.callRet` holds.** -/
theorem callRet_holds : Task.callRet := by
  intro t c o fo fl hCall hlt hC3 hc s s₁ m₁ m₂ hrip _ hl1 hs
  obtain ⟨hw, h1rsp, h1rip, h1oth⟩ := call_law hCall hrip hl1 hs
  refine ⟨hw, h1rsp, h1rip, h1oth, ?_⟩
  intro acc s₂ hX hend hrsp2
  refine ⟨?_, ?_⟩
  · intro m₃ s₃ m₄ _ hl3 hread hs3
    have h2rip : s₂.rip = t.base + BitVec.ofNat 64 (fo + fl) := by
      rw [hend, slice_endRip (by omega)]
    have hr3 : m₃.readBytes (s₂.read .rsp).toNat 8 = some (encodeWords [s.rip + 5]) := by
      rw [hrsp2, h1rsp]; exact hread
    obtain ⟨hr, hrsp, hm, hoth⟩ := ret_law hC3 h2rip hl3 hr3 hs3
    refine ⟨hr, ?_, hm, hoth⟩
    rw [hrsp, hrsp2, h1rsp]; simp
  · intro L hL
    obtain ⟨σ, rs, los, hT, hF, hregs, hskip⟩ := tvCfg_steps hc h1rip hX hL
    rw [hskip hend] at hT
    exact ⟨rs, los, hT, hF, hregs⟩

/-! ## CIR runs compose -/

theorem trun_trans {s rs l s₁ rs₁ l' s₂ rs₂} (h : TRun s rs l s₁ rs₁)
    (h' : TRun s₁ rs₁ l' s₂ rs₂) : TRun s rs (l ++ l') s₂ rs₂ := by
  induction h with
  | refl => exact h'
  | tau hs _ ih => exact .tau hs (ih h')
  | lab hs _ ih => exact .lab hs (ih h')

theorem trun_seqL {s rs l s' rs'} (t : Stmt) (h : TRun s rs l s' rs') :
    TRun (.seq s t) rs l (.seq s' t) rs' := by
  induction h with
  | refl => exact .refl
  | tau hs _ ih => exact .tau (.seq hs) ih
  | lab hs _ ih => exact .lab (.seq hs) ih

/-- A run of `a` to `skip`, then a run of `k`, is a run of `a; k`. -/
theorem trun_seq {a k : Stmt} {rs rs₁ rs₂ : Regs} {l l' : List Lab} {s₂ : Stmt}
    (h : TRun a rs l .skip rs₁) (h' : TRun k rs₁ l' s₂ rs₂) :
    TRun (.seq a k) rs (l ++ l') s₂ rs₂ :=
  trun_trans (trun_seqL k h) (.tau .seqSkip h')

theorem trun_assign {d : Reg} {e : Expr} {rs : Regs} :
    TRun (.assign d e) rs [] .skip (rs.set d (e.eval rs)) := .tau .assign .refl

/-! ## The real machine against validated code -/

/-- The checker against the real machine (`Bridge.tvCfg_real`, re-derived here). -/
theorem tvCfg_real {t : XThread} {c : GCert} (hc : tvCfg t c = true)
    {s₀ s : State} (h0 : s₀.rip = t.base) {xs : List SeqStep} (hr : A9Run t s₀ xs s) {L : Nat}
    (hL : xs.length ≤ L) :
    ∃ acc : List (List XAct), List.Forall₂ ActsOk acc xs ∧
      ∃ σ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s₀) (los.filterMap id) σ rs ∧
        List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los ∧
        regsOf s = rs ∧ (s.rip = t.endRip → σ = .skip) := by
  obtain ⟨acc, hx, hok⟩ := Silmaril.Proofs.X86.Concurrency.Bridge.xrun_of_a9run hr
    fun acc s₁ hx hne m s₂ m₂ hR hl hs =>
      Silmaril.Proofs.X86.Concurrency.Bridge.tvCfgDefined_holds t c hc s₀ s₁ acc h0 hx hne m s₂
        m₂ hR hl hs
  have hlen : acc.length ≤ L := by rw [hok.length_eq]; exact hL
  exact ⟨acc, hok, tvCfg_steps hc h0 hx hlen⟩

theorem forall₂_combine {acc : List (List XAct)} {xs : List SeqStep} {los : List (Option Lab)} :
    List.Forall₂ ActsOk acc xs →
    List.Forall₂ (fun acts o => acts = o.toList.flatMap Lab.acts) acc los →
    List.Forall₂ LObs.Ok (xs.map .step) los := by
  intro h1 h2
  induction h1 generalizing los with
  | nil => cases h2; exact .nil
  | cons ha _ ih =>
    cases h2 with
    | cons hb t2 =>
      refine .cons ?_ (ih t2)
      show ActsOk _ _
      rw [← hb]; exact ha

theorem forall₂_app {α β : Type} {R : α → β → Prop} {a b : List α} {c d : List β}
    (h1 : List.Forall₂ R a c) (h2 : List.Forall₂ R b d) : List.Forall₂ R (a ++ b) (c ++ d) := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

/-- A segment run, to the end of its slice, is a CIR run of its program to `skip`. -/
theorem seg_run {t : XThread} {o n : Nat} {c : GCert} (hseg : segOk t o n c = true)
    {s : State} {xs : List SeqStep} {s' : State} (h0 : s.rip = t.base + BitVec.ofNat 64 o)
    (hr : A9Run (slice t o (o + n)) s xs s') (he : s'.rip = (slice t o (o + n)).endRip)
    {L : Nat} (hL : xs.length ≤ L) :
    ∃ rs, ∃ los : List (Option Lab), TRun (c.body L) (regsOf s) (los.filterMap id) .skip rs ∧
      List.Forall₂ LObs.Ok (xs.map .step) los ∧ regsOf s' = rs ∧
      s'.rip = t.base + BitVec.ofNat 64 (o + n) := by
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq] at hseg
  obtain ⟨hfit, hc⟩ := hseg
  obtain ⟨acc, hok, σ, rs, los, hT, hF, hregs, hskip⟩ := tvCfg_real hc h0 hr hL
  rw [hskip he] at hT
  exact ⟨rs, los, hT, forall₂_combine hok hF, hregs, by rw [he, slice_endRip hfit]⟩

theorem callOk_spec {t : XThread} {o : Nat} {f : Callee} (h : callOk t o f = true) :
    CallAt t o f.off ∧ f.off + f.len < t.code.length ∧ t.code[f.off + f.len]? = some 0xC3 ∧
      tvCfg (slice t f.off (f.off + f.len)) f.cert = true := by
  unfold callOk at h
  split at h
  · rename_i rel hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨htgt, hlt⟩, hC3⟩, hc⟩ := h
    refine ⟨⟨rel, hf, ?_⟩, hlt, hC3, hc⟩
    rw [BitVec.add_assoc, htgt]
  · cases h

/-- **Soundness of the caller checker** against real runs. -/
theorem ltv_sound {t : XThread} :
    ∀ {o : Nat} {ps : List Part} {n : Nat} {c : GCert} {s : State} {obs : List LObs} {s' : State},
      LRun t o ps n c s obs s' → ltvFrom t o ps n c = true →
      s.rip = t.base + BitVec.ofNat 64 o → ∀ L, obs.length ≤ L →
      ∃ rs, ∃ los : List (Option Lab), TRun (lbody L ps c) (regsOf s) (los.filterMap id) .skip rs ∧
        List.Forall₂ LObs.Ok obs los ∧ regsOf s' = rs := by
  intro o ps n c s obs s' hr
  induction hr with
  | last hr he =>
    intro hchk h0 L hL
    simp only [List.length_map] at hL
    obtain ⟨rs, los, hT, hF, hregs, -⟩ := seg_run hchk h0 hr he hL
    exact ⟨rs, los, hT, hF, hregs⟩
  | @call o p ps n c s xs s₁ qc ys s₃ qr zs s' hr he hRc hlc hc hf hfe hRr hlr hslot hret tl ih =>
    intro hchk h0 L hL
    simp only [ltvFrom, Bool.and_eq_true] at hchk
    obtain ⟨⟨hseg, hcall⟩, hrest⟩ := hchk
    simp only [List.length_append, List.length_map, List.length_cons] at hL
    -- the segment
    obtain ⟨rs₁, los₁, hT₁, hF₁, hreg₁, hrip₁⟩ := seg_run hseg h0 hr he (L := L) (by omega)
    -- the call
    obtain ⟨hcallAt, hlt, hC3, hcc⟩ := callOk_spec hcall
    obtain ⟨hw, hrsp₂, hrip₂, hoth₂⟩ := call_law hcallAt hrip₁ hlc hc
    -- the callee
    have hcseg : segOk t p.callee.off p.callee.len p.callee.cert = true := by
      simp only [segOk, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, hcc⟩
    obtain ⟨rs₂, los₂, hT₂, hF₂, hreg₂, hrip₃⟩ := seg_run hcseg hrip₂ hf hfe (L := L) (by omega)
    -- the ret
    obtain ⟨hrip₄, hrsp₄, hm₄, hoth₄⟩ := ret_law hC3 hrip₃ hlr hslot hret
    -- the rest
    have h0' : qr.post.rip = t.base + BitVec.ofNat 64 (o + p.len + 5) := by
      rw [hrip₄, hrip₁, BitVec.ofNat_add (o + p.len) 5, BitVec.add_assoc]; rfl
    obtain ⟨rs₃, los₃, hT₃, hF₃, hreg₃⟩ := ih hrest h0' L (by omega)
    -- the registers at the glue
    have hpush : regsOf qc.post = rs₁.set .rsp (Expr.eval rs₁ (.bin .sub (.reg .rsp) (.lit 8))) := by
      funext r
      rw [← hreg₁]
      by_cases hr : r = Silmaril.X86.Reg.rsp
      · subst hr; simp only [regsOf, Regs.set, ↓reduceIte, Expr.eval, BinOp.eval, hrsp₂]; rfl
      · simp only [regsOf, Regs.set, hr, ↓reduceIte]; exact hoth₂ r hr
    have hpop : regsOf qr.post = rs₂.set .rsp (Expr.eval rs₂ (.bin .add (.reg .rsp) (.lit 8))) := by
      funext r
      rw [← hreg₂]
      by_cases hr : r = Silmaril.X86.Reg.rsp
      · subst hr; simp only [regsOf, Regs.set, ↓reduceIte, Expr.eval, BinOp.eval, hrsp₄]; rfl
      · simp only [regsOf, Regs.set, hr, ↓reduceIte]; exact hoth₄ r hr
    refine ⟨rs₃, (los₁ ++ none :: los₂) ++ none :: los₃, ?_, ?_, hreg₃⟩
    · have hT : TRun (lbody L (p :: ps) c) (regsOf s)
          (los₁.filterMap id ++ ([] ++ (los₂.filterMap id ++ ([] ++ los₃.filterMap id)))) .skip rs₃ := by
        rw [hpush] at hT₂
        rw [hpop] at hT₃
        exact trun_seq hT₁ (trun_seq trun_assign (trun_seq hT₂ (trun_seq trun_assign hT₃)))
      simpa [List.filterMap_append] using hT
    · refine forall₂_app (forall₂_app hF₁ (.cons ⟨rfl, s₁.rip + 5, ?_⟩ hF₂)) (.cons ⟨rfl, hm₄⟩ hF₃)
      rw [hrsp₂]; exact hw

/-- The caller checker reads only the image's code. -/
theorem ltvFrom_code {t t' : XThread} (h : t.code = t'.code) :
    ∀ o ps n c, ltvFrom t o ps n c = ltvFrom t' o ps n c := by
  have hs : ∀ o n c, segOk t o n c = segOk t' o n c := by
    intro o n c
    simp only [segOk, h]
    rw [tvCfg_code (t := slice t o (o + n)) (t' := slice t' o (o + n)) (by simp [slice, h])]
  have hc : ∀ o f, callOk t o f = callOk t' o f := by
    intro o f
    obtain ⟨b, code, R, i⟩ := t
    obtain ⟨b', code', R', i'⟩ := t'
    cases h
    simp only [callOk]
    rw [tvCfg_code (t := slice ⟨b, code, R, i⟩ f.off (f.off + f.len))
      (t' := slice ⟨b', code, R', i'⟩ f.off (f.off + f.len)) rfl]
    rfl
  intro o ps
  induction ps generalizing o with
  | nil => intro n c; exact hs o n c
  | cons p ps ih => intro n c; simp only [ltvFrom, hs, hc, ih]

end Silmaril.Proofs.X86.Concurrency.Bridge.Link
