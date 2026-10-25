module

public import Silmaril.Wasm.Binaryen.Joinable
public import Silmaril.Wasm.Binaryen.SeqTyping
public import Silmaril.Wasm.Validation.Check.ModuleCompleteWf
public import Silmaril.Wasm.Validation.Check.FuncComplete

@[expose] public section

/-! # Contextual refinement without typing side conditions

`SeqRefines R P C it a b` is `SeqOk C a it ∧ SeqOk C b it ∧ CRef R P a b`, where the
third component `CRef` does not mention `C` or `it`. This file develops `CRef`:

* congruence under one-hole contexts (`CRef.plug`) and composition
  (`CRef.trans`, given validity of the intermediate module);
* equal lowerings give `CRef` (`CRef.of_lower_eq`);
* validity of plugged modules is transported along `TyRepl` (`ok_transfer`):
  a module stays valid when a function body is replaced by one that is typed
  wherever the old one is (proved by rebuilding the `ModuleOk` derivation);
* a typing of the hole can be read off any valid plugged module
  (`plug_typing`), so a local fact proved at *every* typing of the hole yields
  `CRef` (`CRef.of_typed_left`/`_right`). This is how the bridges of
  `Joinable.lean`, which are stated at one typing, are applied inside arbitrary
  contexts.

`VEq` packages a rewrite `b ↝ a` (typing preserved, contextual equivalence in both
directions) and `VTnh` its `trapsNeverHappen` variant (one direction, `TrapsUB`);
both are closed under `trans` and `plug`.

**Scope.** This module does not establish the legacy general results `VEq.of_joinable` and
`VTnh.of_joinableTrap`. The toolkit contracts are supplied by separate proof modules.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics Validation

/-! ## Lowering and typing of plugged contexts -/

theorem BCtx.lowerList_plug_eq (K : BCtx) {a b : List BExpr}
    (h : BExpr.lowerList a = BExpr.lowerList b) :
    BExpr.lowerList (K.plug a) = BExpr.lowerList (K.plug b) := by
  induction K <;> simp_all [BCtx.plug, BExpr.lower]

theorem TyRepl.plug (K : BCtx) {a b : List BExpr}
    (h : TyRepl (BExpr.lowerList a) (BExpr.lowerList b)) :
    TyRepl (BExpr.lowerList (K.plug a)) (BExpr.lowerList (K.plug b)) := by
  induction K with
  | hole => exact h
  | seq pre k post ih =>
    simpa [BCtx.plug] using
      TyRepl.append_left (BExpr.lowerList pre) (TyRepl.append_right ih (BExpr.lowerList post))
  | op i pre k post ih =>
    simpa [BCtx.plug] using
      TyRepl.append_left (BExpr.lowerList pre)
        (TyRepl.append_right ih (BExpr.lowerList post ++ [i]))
  | block bt pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.block (TyRepl.append_left (BExpr.lowerList pre)
        (TyRepl.append_right ih (BExpr.lowerList post))) bt
  | loop bt pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.loop (TyRepl.append_left (BExpr.lowerList pre)
        (TyRepl.append_right ih (BExpr.lowerList post))) bt
  | ifCond bt pre k post t e ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.append_left (BExpr.lowerList pre)
        (TyRepl.append_right ih
          (BExpr.lowerList post ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]))
  | ifThen bt c pre k post e ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.append_left (BExpr.lowerList c)
        (TyRepl.if_ (TyRepl.append_left (BExpr.lowerList pre)
          (TyRepl.append_right ih (BExpr.lowerList post)))
          (TyRepl.refl (BExpr.lowerList e)) bt)
  | ifElse bt c t pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.append_left (BExpr.lowerList c)
        (TyRepl.if_ (TyRepl.refl (BExpr.lowerList t))
          (TyRepl.append_left (BExpr.lowerList pre)
            (TyRepl.append_right ih (BExpr.lowerList post))) bt)
  | tryTable bt cs pre k post ih =>
    simpa [BCtx.plug, BExpr.lower] using
      TyRepl.tryTable (TyRepl.append_left (BExpr.lowerList pre)
        (TyRepl.append_right ih (BExpr.lowerList post))) bt cs

/-- A typed middle part of a sequence is typed in some well-formed context. -/
theorem mid_typing {C : Context} {it : InstrType} {A X B : List Instr} (hC : C.Wf)
    (h : InstrsOk C (A ++ (X ++ B)) it) : ∃ C' it', C'.Wf ∧ InstrsOk C' X it' := by
  obtain ⟨t₂, xs₁, xs₂, -, h₂⟩ := InstrsOk.append_inv (is₁ := A) (is₂ := X ++ B) hC h
  obtain ⟨t₃, ys₁, ys₂, h₃, -⟩ := InstrsOk.append_inv (hC.initLocals _) h₂
  exact ⟨_, _, hC.initLocals _, h₃⟩

/-- A typed suffix of a sequence is typed in some well-formed context. -/
theorem last_typing {C : Context} {it : InstrType} {A X : List Instr} (hC : C.Wf)
    (h : InstrsOk C (A ++ X) it) : ∃ C' it', C'.Wf ∧ InstrsOk C' X it' := by
  obtain ⟨t₂, xs₁, xs₂, -, h₂⟩ := InstrsOk.append_inv (is₁ := A) (is₂ := X) hC h
  exact ⟨_, _, hC.initLocals _, h₂⟩

/-- The body of a typed structured instruction is typed in some well-formed context. -/
theorem body_typing {C : Context} {it : InstrType} {i : Instr} {B : List Instr} (hC : C.Wf)
    (h : InstrsOk C [i] it)
    (hi : ∀ C it, C.Wf → InstrOk C i it → ∃ C' it', C'.Wf ∧ InstrsOk C' B it') :
    ∃ C' it', C'.Wf ∧ InstrsOk C' B it' := by
  obtain ⟨ts, it₀, -, hi₀, -⟩ := single_inv' hC h
  exact hi C it₀ hC hi₀

/-- **A typing of the hole** can be read off any typing of a plugged context. -/
theorem plug_typing (K : BCtx) (a : List BExpr) :
    ∀ {C : Context} {it : InstrType}, C.Wf → InstrsOk C (BExpr.lowerList (K.plug a)) it →
      ∃ C' it', C'.Wf ∧ InstrsOk C' (BExpr.lowerList a) it' := by
  induction K with
  | hole => intro C it hC h; exact ⟨C, it, hC, h⟩
  | seq pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it := by
      simpa [BCtx.plug] using h
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC h'
    exact ih hC' h''
  | op i pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ (BExpr.lowerList post ++ [i]))) it := by
      simpa [BCtx.plug] using h
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC h'
    exact ih hC' h''
  | block bt pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C [.block bt (BExpr.lowerList (pre ++ k.plug a ++ post))] it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C₁, it₁, hC₁, h₁⟩ := body_typing hC h' (fun C it hC hi => by
      cases hi with
      | block hbt hb =>
        exact ⟨_, _, wf_withLabel hC (hbt.regular hC).2, hb⟩
      | _ => rename_i h; cases h)
    have h₂ : InstrsOk C₁ (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it₁ := by
      simpa using h₁
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC₁ h₂
    exact ih hC' h''
  | loop bt pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C [.loop bt (BExpr.lowerList (pre ++ k.plug a ++ post))] it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C₁, it₁, hC₁, h₁⟩ := body_typing hC h' (fun C it hC hi => by
      cases hi with
      | loop hbt hb =>
        exact ⟨_, _, wf_withLabel hC (hbt.regular hC).1, hb⟩
      | _ => rename_i h; cases h)
    have h₂ : InstrsOk C₁ (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it₁ := by
      simpa using h₁
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC₁ h₂
    exact ih hC' h''
  | ifCond bt pre k post t e ih =>
    intro C it hC h
    have h' : InstrsOk C (BExpr.lowerList pre ++ (BExpr.lowerList (k.plug a) ++
        (BExpr.lowerList post ++ [.if_ bt (BExpr.lowerList t) (BExpr.lowerList e)]))) it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC h'
    exact ih hC' h''
  | ifThen bt c pre k post e ih =>
    intro C it hC h
    have h' : InstrsOk C (BExpr.lowerList c ++
        [.if_ bt (BExpr.lowerList (pre ++ k.plug a ++ post)) (BExpr.lowerList e)]) it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C₀, it₀, hC₀, h₀⟩ := last_typing hC h'
    obtain ⟨C₁, it₁, hC₁, h₁⟩ := body_typing hC₀ h₀ (fun C it hC hi => by
      cases hi with
      | if_ hbt hb₁ _ =>
        exact ⟨_, _, wf_withLabel hC (hbt.regular hC).2, hb₁⟩
      | _ => rename_i h; cases h)
    have h₂ : InstrsOk C₁ (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it₁ := by
      simpa using h₁
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC₁ h₂
    exact ih hC' h''
  | ifElse bt c t pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C (BExpr.lowerList c ++
        [.if_ bt (BExpr.lowerList t) (BExpr.lowerList (pre ++ k.plug a ++ post))]) it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C₀, it₀, hC₀, h₀⟩ := last_typing hC h'
    obtain ⟨C₁, it₁, hC₁, h₁⟩ := body_typing hC₀ h₀ (fun C it hC hi => by
      cases hi with
      | if_ hbt _ hb₂ =>
        exact ⟨_, _, wf_withLabel hC (hbt.regular hC).2, hb₂⟩
      | _ => rename_i h; cases h)
    have h₂ : InstrsOk C₁ (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it₁ := by
      simpa using h₁
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC₁ h₂
    exact ih hC' h''
  | tryTable bt cs pre k post ih =>
    intro C it hC h
    have h' : InstrsOk C [.tryTable bt cs (BExpr.lowerList (pre ++ k.plug a ++ post))] it := by
      simpa [BCtx.plug, BExpr.lower] using h
    obtain ⟨C₁, it₁, hC₁, h₁⟩ := body_typing hC h' (fun C it hC hi => by
      cases hi with
      | tryTable hbt hb _ =>
        exact ⟨_, _, wf_withLabel hC (hbt.regular hC).2, hb⟩
      | _ => rename_i h; cases h)
    have h₂ : InstrsOk C₁ (BExpr.lowerList pre ++
        (BExpr.lowerList (k.plug a) ++ BExpr.lowerList post)) it₁ := by
      simpa using h₁
    obtain ⟨C', it', hC', h''⟩ := mid_typing hC₁ h₂
    exact ih hC' h''

/-! ## Module validity -/

section ModuleValidity

open ModuleWf

/-- The context of a valid module is well formed. -/
theorem moduleCtx_wf {m : Module} {dts : List DefType} {xtI : List CExternType}
    {jts : List DefType} {gts : List CGlobalType} {tts : List CTableType} {fdts : List DefType}
    {rts : List CRefType}
    (htypes : TypesOk {} m.types dts)
    (himports : List.Forall₂ (ImportOk { types := dts }) m.imports xtI)
    (htags : List.Forall₂ (TagOk (moduleCtx' m dts xtI fdts)) m.tags jts)
    (hglobals : GlobalsOk (moduleCtx' m dts xtI fdts) m.globals gts)
    (htables : List.Forall₂ (TableOk (moduleCtx' m dts xtI fdts)) m.tables tts)
    (hFd : ∀ d ∈ fdts, d ∈ dts)
    (helems : ∀ rt ∈ rts, TyOk ({ types := dts } : TypeCtx) rt) :
    (moduleCtx m (moduleCtx' m dts xtI fdts) xtI jts gts tts rts).Wf := by
  have hΔ := typeCtx_ok htypes
  have hX := externs_tyOk (Δ := { types := dts }) (xs := xtI) (fun xt hxt => by
    obtain ⟨_, _, hi⟩ := forall₂_mem_right himports xt hxt
    exact hi.2)
  obtain ⟨hXt, hXg, hXtb, hXf⟩ := hX
  have hFty : ∀ d ∈ fdts, TyOk ({ types := dts } : TypeCtx) d := fun d hd =>
    (hΔ d (hFd d hd)).2
  refine ⟨hΔ, ?_, ?_, ?_, ?_, by simp [moduleCtx, moduleCtx'], by simp [moduleCtx, moduleCtx'],
    by simp [moduleCtx, moduleCtx'], helems⟩
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hXt d hd
    · obtain ⟨_, _, ht⟩ := forall₂_mem_right htags d hd
      exact ht.2.1
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hXg g hg
    · exact globalsOk_tyOk hglobals rfl g hg
  · intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · exact hXtb t ht
    · obtain ⟨_, _, ht'⟩ := forall₂_mem_right htables t ht
      exact ht'.2.1.2
  · intro d hd
    rcases List.mem_append.1 hd with hd | hd
    · exact hXf d hd
    · exact hFty d hd

/-- The functions of a valid module are valid in a well-formed context. -/
theorem ModuleOk.funcs_wf {M : Module} {mt : CModuleType} (h : ModuleOk M mt) :
    ∃ C fdts, C.Wf ∧ List.Forall₂ (FuncOk C) M.funcs fdts := by
  obtain ⟨htypes, himports, rfl, rfl, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE
  have hW := moduleCtx_wf (rts := rts) (jts := jts) htypes himports htags hglobals htables
    (funcs_mem hfuncs) (by
      intro rt hrt
      obtain ⟨_, _, he⟩ := forall₂_mem_right helems rt hrt
      exact he.2.1)
  exact ⟨_, _, hW, hfuncs⟩

/-- **Replacing the functions of a valid module** by functions valid wherever the old
ones are keeps it valid at the same type. -/
theorem ModuleOk.replaceFuncs {M : Module} {mt : CModuleType} {fs : List Func}
    (h : ModuleOk M mt)
    (hf : ∀ C fdts, C.Wf → List.Forall₂ (FuncOk C) M.funcs fdts →
      List.Forall₂ (FuncOk C) fs fdts) :
    ModuleOk { M with funcs := fs } mt := by
  obtain ⟨htypes, himports, rfl, rfl, htags, hglobals, hmems, htables, hfuncs, hdata,
    helems, hstart, hexports, hnd⟩ := h
  rename_i dts xtI jts gts tts fdts rts xtE
  have hW := moduleCtx_wf (rts := rts) (jts := jts) htypes himports htags hglobals htables
    (funcs_mem hfuncs) (by
      intro rt hrt
      obtain ⟨_, _, he⟩ := forall₂_mem_right helems rt hrt
      exact he.2.1)
  exact ModuleOk.mk htypes himports rfl rfl htags hglobals hmems htables (hf _ _ hW hfuncs) hdata
    helems hstart hexports hnd

/-- A function stays valid when its body is replaced along `TyRepl`. -/
theorem FuncOk.replaceBody {C : Context} (hC : C.Wf) {f : Func} {d : DefType} {body' : Expr}
    (h : FuncOk C f d) (hb : TyRepl f.body body') : FuncOk C { f with body := body' } d := by
  cases h with
  | @mk ps rs lts hd he hl hbody =>
    obtain ⟨hps, hrs⟩ := Expand.func_ok (hC.type hd) he
    exact .mk hd he hl (hb _ _ (hC.funcBody hps hrs (locals_tyOk hl)) hbody)

theorem forall₂_map_modifyAt {α β γ : Type _} {R : γ → β → Prop} {k : α → γ} {F G : α → α}
    (hFG : ∀ x d, R (k (F x)) d → R (k (G x)) d) :
    ∀ (g : Nat) {L : List α} {M : List β}, List.Forall₂ R ((modifyAt F g L).map k) M →
      List.Forall₂ R ((modifyAt G g L).map k) M
  | _, [], _, h => by simpa [modifyAt] using h
  | 0, a :: L, M, h => by
    cases M with
    | nil => simp [modifyAt] at h
    | cons d M =>
      simp only [modifyAt, List.map_cons, List.forall₂_cons] at h ⊢
      exact ⟨hFG _ _ h.1, h.2⟩
  | g + 1, a :: L, M, h => by
    cases M with
    | nil => simp [modifyAt] at h
    | cons d M =>
      simp only [modifyAt, List.map_cons, List.forall₂_cons] at h ⊢
      exact ⟨h.1, forall₂_map_modifyAt hFG g h.2⟩

/-- **Validity is transported along `TyRepl`** of a function body. -/
theorem ok_transfer {m : BModule} {g : Nat} {B B' : List BExpr}
    (h : TyRepl (BExpr.lowerList B) (BExpr.lowerList B')) (hm : (m.withBody g B).Ok) :
    (m.withBody g B').Ok := by
  obtain ⟨t, ht⟩ := hm
  refine ⟨t, ?_⟩
  have := ModuleOk.replaceFuncs
    (fs := (modifyAt (fun f => { f with body := B' }) g m.funcs).map
      (Declaration.Func.mapBody BExpr.lowerList)) ht (fun C fdts hC hf =>
        forall₂_map_modifyAt (fun x d hx => by
          simpa [Declaration.Func.mapBody] using
            FuncOk.replaceBody hC (body' := BExpr.lowerList B') hx
              (by simpa [Declaration.Func.mapBody] using h)) g hf)
  exact this

/-- A plugged body of a valid module is typed in a well-formed context, when the index
is in range. -/
theorem funcBody_typed {m : BModule} {g : Nat} {B : List BExpr} (hg : g < m.funcs.length)
    (hm : (m.withBody g B).Ok) : ∃ C it, C.Wf ∧ InstrsOk C (BExpr.lowerList B) it := by
  obtain ⟨t, ht⟩ := hm
  obtain ⟨C, fdts, hC, hf⟩ := ModuleOk.funcs_wf ht
  have key : ∀ (L : List BFunc) (g : Nat) (M : List DefType), g < L.length →
      List.Forall₂ (FuncOk C)
        ((modifyAt (fun f => { f with body := B }) g L).map
          (Declaration.Func.mapBody BExpr.lowerList)) M →
      ∃ C it, C.Wf ∧ InstrsOk C (BExpr.lowerList B) it := by
    intro L
    induction L with
    | nil => intro g M hg; simp at hg
    | cons a L ih =>
      intro g M hg hM
      cases M with
      | nil => cases g <;> simp [modifyAt] at hM
      | cons d M =>
        cases g with
        | zero =>
          simp only [modifyAt, List.map_cons, List.forall₂_cons] at hM
          cases hM.1 with
          | @mk ps rs lts hd he hl hbody =>
            obtain ⟨hps, hrs⟩ := Expand.func_ok (hC.type hd) he
            exact ⟨_, _, hC.funcBody hps hrs (locals_tyOk hl), hbody⟩
        | succ g =>
          simp only [modifyAt, List.map_cons, List.forall₂_cons] at hM
          exact ih g M (by simpa using hg) hM.2
  exact key m.funcs g fdts hg hf

/-- Out of range, `withBody` changes nothing. -/
theorem withBody_out {m : BModule} {g : Nat} (hg : ¬ g < m.funcs.length) (B B' : List BExpr) :
    m.withBody g B = m.withBody g B' := by
  have key : ∀ (L : List BFunc) (g : Nat), ¬ g < L.length →
      modifyAt (fun f => { f with body := B }) g L = modifyAt (fun f => { f with body := B' }) g L
    := by
    intro L
    induction L with
    | nil => intro g _; cases g <;> rfl
    | cons a L ih =>
      intro g hg
      cases g with
      | zero => simp at hg
      | succ g => simp only [modifyAt]; rw [ih g (by simpa using hg)]
  simp only [BModule.withBody, key m.funcs g hg]

theorem withBody_lower_congr (m : BModule) (g : Nat) {B B' : List BExpr}
    (h : BExpr.lowerList B = BExpr.lowerList B') :
    (m.withBody g B).lower = (m.withBody g B').lower := by
  have key : ∀ (L : List BFunc) (g : Nat),
      (modifyAt (fun f => { f with body := B }) g L).map (Declaration.Func.mapBody BExpr.lowerList)
        = (modifyAt (fun f => { f with body := B' }) g L).map
          (Declaration.Func.mapBody BExpr.lowerList) := by
    intro L
    induction L with
    | nil => intro g; cases g <;> rfl
    | cons a L ih =>
      intro g
      cases g with
      | zero => simp [modifyAt, Declaration.Func.mapBody, h]
      | succ g => simp only [modifyAt, List.map_cons, ih g]
  simp only [BModule.lower, BModule.withBody, key m.funcs g]

end ModuleValidity

/-! ## `CRef` -/

/-- The contextual part of `SeqRefines` (with the host's state type explicit). -/
def CRef (R : Behaviour Val → Behaviour Val → Prop) (P : Profile) (a b : List BExpr) : Prop :=
  ∀ (H : Type) (host : HostSemantics H) (m : BModule) (g : Nat) (K : BCtx),
    HostRespectsCode host →
    (m.withBody g (K.plug a)).Ok → (m.withBody g (K.plug b)).Ok →
    ExportRefines R P host (m.withBody g (K.plug a)).lower (m.withBody g (K.plug b)).lower

namespace CRef

variable {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}

theorem of_seqRefines {C : Context} {it : InstrType} {a b : List BExpr}
    (h : SeqRefines R P C it a b) : CRef R P a b :=
  fun _ host m g K hh ha hb => h.2.2 host m g K hh ha hb

theorem plug {a b : List BExpr} (h : CRef R P a b) (K : BCtx) :
    CRef R P (K.plug a) (K.plug b) := by
  intro H host m g K' hh h₁ h₂
  have := h H host m g (K'.comp K) hh (by simpa using h₁) (by simpa using h₂)
  simpa using this

theorem trans (hR : ∀ x y z, R x y → R y z → R x z) {a b c : List BExpr}
    (h₁ : CRef R P a b) (h₂ : CRef R P b c)
    (hok : ∀ (m : BModule) (g : Nat) (K : BCtx), (m.withBody g (K.plug a)).Ok →
      (m.withBody g (K.plug c)).Ok → (m.withBody g (K.plug b)).Ok) : CRef R P a c :=
  fun H host m g K hh ha hc =>
    (h₁ H host m g K hh ha (hok m g K ha hc)).trans hR (h₂ H host m g K hh (hok m g K ha hc) hc)

theorem of_lower_eq (hR : ∀ b, R b b) {a b : List BExpr}
    (h : BExpr.lowerList a = BExpr.lowerList b) : CRef R P a b := by
  intro H host m g K _ _ _
  rw [withBody_lower_congr m g (K.lowerList_plug_eq h)]
  exact ExportRefines.refl hR _

/-- A local fact at every typing of the right-hand side gives `CRef`. -/
theorem of_typed_right (hR : ∀ b, R b b) {a b : List BExpr}
    (h : ∀ C it, C.Wf → InstrsOk C (BExpr.lowerList b) it → CRef R P a b) : CRef R P a b := by
  intro H host m g K hh ha hb
  by_cases hg : g < m.funcs.length
  · obtain ⟨C₀, it₀, hC₀, h₀⟩ := funcBody_typed hg hb
    obtain ⟨C, it, hC, hty⟩ := plug_typing K b hC₀ h₀
    exact h C it hC hty H host m g K hh ha hb
  · rw [withBody_out hg (K.plug a) (K.plug b)]
    exact ExportRefines.refl hR _

/-- A local fact at every typing of the left-hand side gives `CRef`. -/
theorem of_typed_left (hR : ∀ b, R b b) {a b : List BExpr}
    (h : ∀ C it, C.Wf → InstrsOk C (BExpr.lowerList a) it → CRef R P a b) : CRef R P a b := by
  intro H host m g K hh ha hb
  by_cases hg : g < m.funcs.length
  · obtain ⟨C₀, it₀, hC₀, h₀⟩ := funcBody_typed hg ha
    obtain ⟨C, it, hC, hty⟩ := plug_typing K a hC₀ h₀
    exact h C it hC hty H host m g K hh ha hb
  · rw [withBody_out hg (K.plug a) (K.plug b)]
    exact ExportRefines.refl hR _

theorem mono {R' : Behaviour Val → Behaviour Val → Prop} (hRR : ∀ x y, R x y → R' x y)
    {a b : List BExpr} (h : CRef R P a b) : CRef R' P a b :=
  fun H host m g K hh ha hb => (h H host m g K hh ha hb).mono hRR

end CRef

/-- `SeqRefines` from its typing components and `CRef`. -/
theorem SeqRefines.of_cref {R : Behaviour Val → Behaviour Val → Prop} {P : Profile}
    {C : Context} {it : InstrType} {a b : List BExpr} (ha : SeqOk C a it) (hb : SeqOk C b it)
    (h : CRef R P a b) : SeqRefines R P C it a b :=
  ⟨ha, hb, fun host m g K hh h₁ h₂ => h _ host m g K hh h₁ h₂⟩

/-! ## Typed rewrites -/

/-- **An equivalence rewrite** `b ↝ a`: `a` is typed wherever `b` is, and the two are
contextually equivalent. -/
structure VEq (P : Profile) (a b : List BExpr) : Prop where
  ty : TyRepl (BExpr.lowerList b) (BExpr.lowerList a)
  fwd : CRef (· = ·) P a b
  bwd : CRef (fun x y => y = x) P b a

/-- **A `trapsNeverHappen` rewrite** `b ↝ a`: `a` is typed wherever `b` is and refines
it under `TrapsUB`. -/
structure VTnh (P : Profile) (a b : List BExpr) : Prop where
  ty : TyRepl (BExpr.lowerList b) (BExpr.lowerList a)
  fwd : CRef TrapsUB P a b

theorem plug_ok {m : BModule} {g : Nat} {K : BCtx} {a b : List BExpr}
    (h : TyRepl (BExpr.lowerList b) (BExpr.lowerList a)) (hb : (m.withBody g (K.plug b)).Ok) :
    (m.withBody g (K.plug a)).Ok :=
  ok_transfer (TyRepl.plug K h) hb

namespace VEq

variable {P : Profile}

theorem refl (a : List BExpr) : VEq P a a :=
  ⟨TyRepl.refl _, CRef.of_lower_eq (R := (· = ·)) (fun _ => rfl) rfl,
    CRef.of_lower_eq (R := fun x y => y = x) (fun _ => rfl) rfl⟩

theorem of_lower_eq {a b : List BExpr} (h : BExpr.lowerList a = BExpr.lowerList b) :
    VEq P a b :=
  ⟨by rw [h]; exact TyRepl.refl _, CRef.of_lower_eq (R := (· = ·)) (fun _ => rfl) h,
    CRef.of_lower_eq (R := fun x y => y = x) (fun _ => rfl) h.symm⟩

theorem trans {a b c : List BExpr} (h₁ : VEq P a b) (h₂ : VEq P b c) : VEq P a c :=
  ⟨h₂.ty.trans h₁.ty,
   CRef.trans (R := (· = ·)) (fun _ _ _ h h' => h.trans h') h₁.fwd h₂.fwd
     (fun _ _ _ _ hc => plug_ok h₂.ty hc),
   CRef.trans (R := fun x y => y = x) (fun _ _ _ h h' => h'.trans h) h₂.bwd h₁.bwd
     (fun _ _ _ hc _ => plug_ok h₂.ty hc)⟩

theorem plug {a b : List BExpr} (h : VEq P a b) (K : BCtx) : VEq P (K.plug a) (K.plug b) :=
  ⟨TyRepl.plug K h.ty, CRef.plug h.fwd K, CRef.plug h.bwd K⟩

end VEq

namespace VTnh

variable {P : Profile}

theorem of_veq {a b : List BExpr} (h : VEq P a b) : VTnh P a b :=
  ⟨h.ty, CRef.mono (R := (· = ·)) (R' := TrapsUB) (fun _ _ e => TrapsUB.of_eq e) h.fwd⟩

theorem refl (a : List BExpr) : VTnh P a a := of_veq (VEq.refl a)

theorem trans {a b c : List BExpr} (h₁ : VTnh P a b) (h₂ : VTnh P b c) : VTnh P a c :=
  ⟨h₂.ty.trans h₁.ty,
   CRef.trans (R := TrapsUB) (fun _ _ _ h h' => TrapsUB.trans h h') h₁.fwd h₂.fwd
     (fun _ _ _ _ hc => plug_ok h₂.ty hc)⟩

theorem plug {a b : List BExpr} (h : VTnh P a b) (K : BCtx) : VTnh P (K.plug a) (K.plug b) :=
  ⟨TyRepl.plug K h.ty, CRef.plug h.fwd K⟩

end VTnh

end Silmaril.Wasm.Binaryen
