module

public import Silmaril.Wasm.Binaryen.SeqTyping
public import Silmaril.Wasm.Validation.Check.ModuleCompleteWf
public import Silmaril.Wasm.Validation.Check.FuncComplete

@[expose] public section

/-! # One-hole contexts and their typing

`BCtx` (one-hole contexts over folded trees) with `plug`/`comp`, and the typing
facts `SeqRefines.everywhere` (`Binaryen/Equiv.lean`) needs: a typing of the hole
can be read off a typing of a plugged context, typing-preserving replacement is a
congruence for plugging, and a module stays valid when a body is replaced along
`TyRepl`. The typing facts duplicate those of `Binaryen/CtxRefines.lean` (which
imports `Equiv.lean` and so cannot be imported by it), under the namespace
`CtxTyping`.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-! ## Expression level: one-hole contexts -/

/-- One-hole contexts over folded trees. The hole stands for a *list* of trees. -/
inductive BCtx where
  | hole
  | seq (pre : List BExpr) (k : BCtx) (post : List BExpr)
  | op (i : Instr) (pre : List BExpr) (k : BCtx) (post : List BExpr)
  | block (bt : BlockType) (pre : List BExpr) (k : BCtx) (post : List BExpr)
  | loop (bt : BlockType) (pre : List BExpr) (k : BCtx) (post : List BExpr)
  | ifCond (bt : BlockType) (pre : List BExpr) (k : BCtx) (post : List BExpr) (thn els : List BExpr)
  | ifThen (bt : BlockType) (cond pre : List BExpr) (k : BCtx) (post : List BExpr)
      (els : List BExpr)
  | ifElse (bt : BlockType) (cond thn pre : List BExpr) (k : BCtx) (post : List BExpr)
  | tryTable (bt : BlockType) (cs : List Catch) (pre : List BExpr) (k : BCtx) (post : List BExpr)

namespace BCtx

/-- Fill the hole. -/
def plug : BCtx → List BExpr → List BExpr
  | .hole, es => es
  | .seq pre k post, es => pre ++ k.plug es ++ post
  | .op i pre k post, es => [.op i (pre ++ k.plug es ++ post)]
  | .block bt pre k post, es => [.block bt (pre ++ k.plug es ++ post)]
  | .loop bt pre k post, es => [.loop bt (pre ++ k.plug es ++ post)]
  | .ifCond bt pre k post t e, es => [.if_ bt (pre ++ k.plug es ++ post) t e]
  | .ifThen bt c pre k post e, es => [.if_ bt c (pre ++ k.plug es ++ post) e]
  | .ifElse bt c t pre k post, es => [.if_ bt c t (pre ++ k.plug es ++ post)]
  | .tryTable bt cs pre k post, es => [.tryTable bt cs (pre ++ k.plug es ++ post)]

/-- Context composition: `(K.comp K').plug es = K.plug (K'.plug es)`. -/
def comp : BCtx → BCtx → BCtx
  | .hole, K' => K'
  | .seq pre k post, K' => .seq pre (k.comp K') post
  | .op i pre k post, K' => .op i pre (k.comp K') post
  | .block bt pre k post, K' => .block bt pre (k.comp K') post
  | .loop bt pre k post, K' => .loop bt pre (k.comp K') post
  | .ifCond bt pre k post t e, K' => .ifCond bt pre (k.comp K') post t e
  | .ifThen bt c pre k post e, K' => .ifThen bt c pre (k.comp K') post e
  | .ifElse bt c t pre k post, K' => .ifElse bt c t pre (k.comp K') post
  | .tryTable bt cs pre k post, K' => .tryTable bt cs pre (k.comp K') post

@[simp] theorem plug_comp (K K' : BCtx) (es : List BExpr) :
    (K.comp K').plug es = K.plug (K'.plug es) := by
  induction K <;> simp [comp, plug, *]

end BCtx

namespace CtxTyping

theorem lowerList_plug_eq (K : BCtx) {a b : List BExpr}
    (h : BExpr.lowerList a = BExpr.lowerList b) :
    BExpr.lowerList (K.plug a) = BExpr.lowerList (K.plug b) := by
  induction K <;> simp_all [BCtx.plug, BExpr.lower]

theorem tyRepl_plug (K : BCtx) {a b : List BExpr}
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

end ModuleValidity

end CtxTyping

end Silmaril.Wasm.Binaryen
