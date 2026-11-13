module

public import Silmaril.Proofs.Wasm.Models.FXPresI.ProgCase

/-!
# Progress for `envP`: the FX and control instruction cases

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXBindT Silmaril.Wasm.Models.FXResume
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI Silmaril.Proofs.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {s : Store H} {Γ : List TypeIdx}
  {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX} {K : List (Option ContFX)}

/-- Every typed slot of `K` exists (what progress uses of `KOk`). -/
def SlotsOk (Γ : List TypeIdx) (K : List (Option ContFX)) : Prop :=
  ∀ (k : Nat) (ct : TypeIdx), Γ[k]? = some ct →
    K[k]? = some none ∨ ∃ C : ContFX, K[k]? = some (some C)

theorem tag_of {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst} (hf : f.module = m₀)
    (hx : m₀.tags[x.toNat]? = some ta) (ht : s.tags[ta]? = some ti) :
    s.tag? f x = some (ta, ti) := by
  simp [Store.tag?, hf, hx, ht]

theorem contParams_of {ct : TypeIdx} {ps rs : List CValType}
    (h : contType? m₀ ct = some (ps, rs)) : contParams? m₀ ct = some ps := by
  have e : contParams? m₀ ct = (contType? m₀ ct).map Prod.fst := rfl
  rw [e, h]
  rfl

theorem resolve_all {f : Frame} {Ls : List (List FTy)} {ts : List FTy} {hs : List OnClause}
    (hf : f.module = m₀) (hh : ∀ c ∈ hs, OnClauseOk (envP m₀) s Ls ts c) :
    ∃ hs', hs.mapM (resolve s f) = some hs' := by
  induction hs with
  | nil => exact ⟨[], rfl⟩
  | cons c hs ih =>
    obtain ⟨hs', e⟩ := ih fun c hc => hh c (List.mem_cons_of_mem _ hc)
    have hc := hh c List.mem_cons_self
    cases c with
    | onLabel x l =>
      obtain ⟨ta, hx, ti, -, -, -, -, ht, -⟩ := hc
      exact ⟨.onLabel ta l :: hs', by simp [List.mapM_cons, resolve, tag_of hf hx ht, e]⟩
    | onSwitch x => exact hc.elim

/-- The last value is a continuation reference at `ct`, the others are typed by `a`. -/
theorem split_cont {vs₂ : List FVal} {a : List FTy} {ct : TypeIdx}
    (h : ValsTy (envP m₀) s Γ vs₂ (a ++ [.cont ct])) :
    ∃ ws k, vs₂ = ws ++ [.cont k] ∧ ValsTy (envP m₀) s Γ ws a ∧ Γ[k]? = some ct := by
  obtain ⟨ws, vs₃, rfl, h₁, h₂⟩ := valsTy_split h
  obtain ⟨v, rfl⟩ : ∃ v, vs₃ = [v] := by cases h₂ with | cons _ h => cases h; exact ⟨_, rfl⟩
  obtain ⟨k, rfl, hk⟩ := vty_cont (List.forall₂_cons.1 h₂).1
  exact ⟨ws, k, rfl, h₁, hk⟩

theorem fvals_cont (ws : List FVal) (k : Nat) (x : AdminFX) :
    fvals (ws ++ [.cont k]) ++ [x] = fvals ws ++ [.contRef k, x] := by
  simp [fvals, FVal.toAdmin]

theorem pg_contNew {ct : TypeIdx} {as : List AdminFX} {pre : List FTy} :
    PG P host fx m₀ s Γ K (.fx (.contNew ct) :: as) (pre ++ [ntP ct]) :=
  pg_win fun _ vs₂ _ h => by
    cases h with
    | cons hv _ => exact (vty_ntP hv).elim

theorem pg_contBind {ct ct' : TypeIdx} {ps₁ ps₂ rs : List CValType} {as : List AdminFX}
    {pre : List FTy} (hK : SlotsOk Γ K) (h : contType? m₀ ct = some (ps₁ ++ ps₂, rs))
    (h' : contType? m₀ ct' = some (ps₂, rs)) :
    PG P host fx m₀ s Γ K (.fx (.contBind ct ct') :: as) (pre ++ vtys ps₁ ++ [.cont ct]) := by
  rw [List.append_assoc]
  refine pg_win fun f vs₂ hf hv => ?_
  obtain ⟨ws, k, rfl, hws, hk⟩ := split_cont hv
  have ha : BindArity f.module ct ct' ws.length := by
    refine ⟨_, _, hf ▸ contParams_of h, hf ▸ contParams_of h', ?_⟩
    simp [valsTy_length hws, vtys]
  rw [fvals_cont]
  rcases hK k ct hk with hn | ⟨C, hC⟩
  · exact ⟨_, .contBindUsed hn ha⟩
  · exact ⟨_, .contBind hC ha⟩

theorem pg_resume {ct : TypeIdx} {hs : List OnClause} {ps rs : List CValType}
    {as : List AdminFX} {pre : List FTy} {Ls : List (List FTy)} (hK : SlotsOk Γ K)
    (h : contType? m₀ ct = some (ps, rs))
    (hh : ∀ c ∈ hs, OnClauseOk (envP m₀) s Ls (vtys rs) c) :
    PG P host fx m₀ s Γ K (.fx (.resume ct hs) :: as) (pre ++ vtys ps ++ [.cont ct]) := by
  rw [List.append_assoc]
  refine pg_win fun f vs₂ hf hv => ?_
  obtain ⟨ws, k, rfl, hws, hk⟩ := split_cont hv
  have ha : ResumeArity f.module ct ws.length :=
    ⟨_, hf ▸ contParams_of h, by simp [valsTy_length hws, vtys]⟩
  obtain ⟨hs', hr⟩ := resolve_all (f := f) hf hh
  rw [fvals_cont]
  rcases hK k ct hk with hn | ⟨C, hC⟩
  · exact ⟨_, .resumeUsed hn ha⟩
  · exact ⟨_, .resume hC hr ha⟩

/-- `suspend`: an unhandled suspension. -/
theorem pg_suspend {x : TagIdx} {tp tr : List CValType} {ta : Nat} {ti : TagInst}
    {as : List AdminFX} {pre : List FTy} (hx : m₀.tags[x.toNat]? = some ta)
    (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some (tp, tr)) :
    PG P host fx m₀ s Γ K (.fx (.suspend x) :: as) (pre ++ vtys tp) := by
  intro f vs hf hvs
  obtain ⟨vs₁, vs₂, rfl, -, h₂⟩ := valsTy_split hvs
  have hl : vs₂.length = tp.length := by simp [valsTy_length h₂, vtys]
  have hH := Halt.suspend (K := K) (E := .seq vs₁ .hole as) (vs := vs₂) (x := x)
    (tag_of hf hx ht) (by simp [CtxV.Handles]) ⟨tp, tr, htt, hl.symm⟩
  exact .inl (by simpa [CtxV.plug, fvals_append] using hH)

/-- `resume_throw`: steps, or halts on a consumed continuation. -/
theorem pg_resumeThrow {ct : TypeIdx} {x : TagIdx} {hs : List OnClause}
    {rs tp tr : List CValType} {ta : Nat} {ti : TagInst} {as : List AdminFX} {pre : List FTy}
    {Ls : List (List FTy)} (hK : SlotsOk Γ K) (hx : m₀.tags[x.toNat]? = some ta)
    (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some (tp, tr))
    (hh : ∀ c ∈ hs, OnClauseOk (envP m₀) s Ls (vtys rs) c) :
    PG P host fx m₀ s Γ K (.fx (.resumeThrow ct x hs) :: as) (pre ++ vtys tp ++ [.cont ct]) := by
  intro f vs hf hvs
  rw [List.append_assoc] at hvs
  obtain ⟨vs₁, vs₂, rfl, -, h₂⟩ := valsTy_split hvs
  obtain ⟨ws, k, rfl, hws, hk⟩ := split_cont h₂
  obtain ⟨ws', rfl⟩ := valsTy_core hws
  have hcode : fvals (vs₁ ++ (liftV ws' ++ [.cont k])) ++ .fx (.resumeThrow ct x hs) :: as =
      fvals vs₁ ++ (cvals ws' ++ [.contRef k, .fx (.resumeThrow ct x hs)]) ++ as := by
    rw [fvals_append, fvals_append, Silmaril.Wasm.Models.FXV.fvals_liftV]
    simp [fvals, FVal.toAdmin]
  rw [hcode]
  rcases hK k ct hk with hn | ⟨C, hC⟩
  · have hH := Halt.usedThrow (s := s) (f := f) (E := .seq vs₁ .hole as) (ws := ws') (ct := ct)
      (x := x) (hs := hs) hn
    exact .inl (by simpa [CtxV.plug] using hH)
  · obtain ⟨hs', hr⟩ := resolve_all (f := f) hf hh
    have hl := valsTy_length hws
    have ha : TagArity ti ws'.length := ⟨tp, tr, htt, by simpa [vtys, liftV] using hl.symm⟩
    exact .inr (step_ctx vs₁ as ⟨_, .resumeThrow hC (tag_of hf hx ht) hr ha⟩)

theorem pg_block {bt : BlockType} {body : List InstrFX} {t₁ t₂ : List CValType}
    {as : List AdminFX} {pre : List FTy} (hb : m₀.blockType? bt = some (t₁, t₂)) :
    PG P host fx m₀ s Γ K (.block bt body :: as) (pre ++ vtys t₁) :=
  pg_win fun _ _ hf hv => ⟨_, .block (hf ▸ hb) (by simp [valsTy_length hv, vtys])⟩

theorem pg_loop {bt : BlockType} {body : List InstrFX} {t₁ t₂ : List CValType}
    {as : List AdminFX} {pre : List FTy} (hb : m₀.blockType? bt = some (t₁, t₂)) :
    PG P host fx m₀ s Γ K (.loop bt body :: as) (pre ++ vtys t₁) :=
  pg_win fun _ _ hf hv => ⟨_, .loop (hf ▸ hb) (by simp [valsTy_length hv, vtys])⟩

theorem pg_if {bt : BlockType} {b₁ b₂ : List InstrFX} {t₁ : List CValType}
    {as : List AdminFX} {pre : List FTy} :
    PG P host fx m₀ s Γ K (.if_ bt b₁ b₂ :: as) (pre ++ vtys t₁ ++ [condTy]) := by
  refine pg_win fun _ vs₂ _ hv => ?_
  obtain ⟨v, rfl⟩ : ∃ v, vs₂ = [v] := by cases hv with | cons _ h => cases h; exact ⟨_, rfl⟩
  obtain ⟨c, rfl⟩ := vty_int (it := .i32) (List.forall₂_cons.1 hv).1
  by_cases hc : c = 0
  · subst hc
    exact ⟨_, .ifFalse⟩
  · exact ⟨_, .ifTrue hc⟩

theorem pg_br {l : LabelIdx} {as : List AdminFX} {i : List FTy} :
    PG P host fx m₀ s Γ K (.core (.plain (.br l)) :: as) i :=
  fun _ vs _ _ => .inl (by simpa using Halt.br vs l as)

theorem pg_ret {as : List AdminFX} {i : List FTy} :
    PG P host fx m₀ s Γ K (.core (.plain .return_) :: as) i :=
  fun _ vs _ _ => .inl (by simpa using Halt.ret vs as)

end Silmaril.Proofs.Wasm.Models.FXPresI
