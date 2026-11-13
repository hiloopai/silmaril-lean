module

public import Silmaril.Wasm.Game.SpecGlobals.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# Spec preparation against single allocation

**Copied** from `Silmaril.Proofs.Wasm.Game.SpecGlobals.Inst`, with `Store Nat`,
`Config Nat` and `FuncInst Nat` replaced by
`Store H`, `Config H` and `FuncInst H` (`variable {H : Type}`), in this topic's namespace; the
proofs are unchanged. The original is stated at `Nat` only; nothing in it uses `Nat`. The
copy is what lets `V2CoreSpecH.Main` state the spec-inclusion at every host type.

`prepare_once`: for a module without data and element segments and without global imports,
instantiated into stores `s` and `t` related by a global embedding `ι` (`Emb ι Univ s t`, the
function modules of `s` naming only existing globals), silmaril-lean's single allocation
`instantiateOnce? s m xas` and the specification's preparation `prepare? evalConst? t m xas`
(`$evalglobals`, then `$allocmodule` allocating every global again) give stores related by a
global embedding `ι'` extending `ι` (`shiftMap`: the once-store's new globals go to the spec's
second copies), frames related by `frame ι'`, empty segment code and the same start function.

Steps: constant evaluation commutes with embeddings (`constInstr?_repl`, `constExpr?_emb`,
`evalConst?_emb`), then `$evalglobals` (`evalGlobals?_emb`, both sides allocating the
initialiser copies), `$evalexprs` (`evalExprs?_emb`, `evalExprss?_emb`), and `$allocmodule`
twice against the residue's allocation once (`allocModule?_twice`, via the closed forms
`allocModule?_inv'`/`allocModule?_of` of silmaril-lean's `allocModule?_inv`).
`modDom_of_storeOk`: in a well-typed host-free store, function modules name existing globals.

Proofs as in the original; they use silmaril-lean's `instantiateOnce?` shape lemmas
(`evalGlobals?_shape`, `evalGlobals?_initial`, `allocModule?_inv`, `allocMany_*_eq`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpecH

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Proofs.Wasm.Game.SpecGlobals

variable {H : Type}

/-! ## Well-typed stores -/

theorem forall₂_left {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b, R a b := by
  induction h with
  | nil => cases ha
  | cons hr _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨_, hr⟩
    · exact ih ha'

theorem externAddrOk_global_lt {s : Store H} {xa : ExternAddr} {xt : CExternType}
    (h : ExternAddrOk s xa xt) : ∀ a, xa = .global a → a < s.globals.length := by
  induction h with
  | global h =>
    intro a ha
    cases ha
    exact (List.getElem?_eq_some_iff.1 h).1
  | sub _ _ _ ih => exact ih
  | _ => intro a ha; cases ha

theorem modDom_of_moduleInstOk {s : Store H} {mi : ModuleInst} {C : Context}
    (h : ModuleInstOk s mi C) : ModDom (· < s.globals.length) mi := by
  cases h with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexp hk =>
    have hg : ∀ a ∈ mi.globals, a < s.globals.length := by
      intro a ha
      obtain ⟨g, hag⟩ := forall₂_left hglobals ha
      exact externAddrOk_global_lt hag a rfl
    refine ⟨hg, fun e he a ha => hg a ?_⟩
    have hm := hexp e he
    rw [ha] at hm
    simpa using hm

/-- Function modules of a well-typed store only name existing globals. -/
theorem modDom_of_storeOk {s : Store H} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f) :
    ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module := by
  intro fi hfi
  cases hs.funcs fi hfi with
  | wasm _ hm _ _ _ => exact modDom_of_moduleInstOk hm
  | host _ _ hc =>
    obtain ⟨f, hf⟩ := hw fi hfi
    rw [hf] at hc
    cases hc


/-! ## Constant evaluation on embedded stores -/

/-- Replace the globals and functions of a store. -/
def repl (G : List GlobalInst) (F : List (FuncInst H)) (u : Store H) : Store H :=
  { u with globals := G, funcs := F }

theorem constInstr?_repl_globalGet {ρ : Nat → Nat} {s : Store H} {f : Frame} {vs : List Val}
    {x : GlobalIdx} (G : List GlobalInst) (F : List (FuncInst H))
    (hG : ((repl G F s).global? (frame ρ f) x).map (·.2) = (s.global? f x).map (·.2)) :
    constInstr? (repl G F s) (frame ρ f) vs (.globalGet x) =
      (constInstr? s f vs (.globalGet x)).map (fun p => (repl G F p.1, p.2)) := by
  simp only [constInstr?, Option.bind_eq_bind]
  cases h1 : s.global? f x <;> cases h2 : (repl G F s).global? (frame ρ f) x <;>
    simp_all [Option.map]

theorem constInstr?_repl_intBinOp {ρ : Nat → Nat} {s : Store H} {f : Frame} {vs : List Val}
    {t : IntType} {op : IntBinOp} (G : List GlobalInst) (F : List (FuncInst H)) :
    constInstr? (repl G F s) (frame ρ f) vs (.intBinOp t op) =
      (constInstr? s f vs (.intBinOp t op)).map (fun p => (repl G F p.1, p.2)) := by
  simp only [constInstr?]
  split
  · rcases pop2? vs with _ | ⟨pre, v₁, v₂⟩
    · rfl
    show ((Val.int? t v₁).bind fun x => (Val.int? t v₂).bind fun y => _) =
      Option.map _ ((Val.int? t v₁).bind fun x => (Val.int? t v₂).bind fun y => _)
    rcases Val.int? t v₁ with _ | x
    · rfl
    rcases Val.int? t v₂ with _ | y
    · rfl
    show (match Numerics.intBinOp t op x y with | .ok z => _ | .error _ => none) =
      Option.map _ (match Numerics.intBinOp t op x y with | .ok z => _ | .error _ => none)
    split <;> rfl
  · rfl

theorem constInstr?_repl {ρ : Nat → Nat} {s : Store H} {f : Frame} {vs : List Val} {i : Instr}
    (G : List GlobalInst) (F : List (FuncInst H))
    (hG : ∀ x, ((repl G F s).global? (frame ρ f) x).map (·.2) = (s.global? f x).map (·.2)) :
    constInstr? (repl G F s) (frame ρ f) vs i =
      (constInstr? s f vs i).map (fun p => (repl G F p.1, p.2)) := by
  cases i
  case globalGet x => exact constInstr?_repl_globalGet G F (hG x)
  case intBinOp t op => exact constInstr?_repl_intBinOp G F
  all_goals simp [constInstr?, structNew?, arrayNewFixed?, Frame.type?, frame, moduleView, repl,
    Store.addStruct, Store.addArray, Option.map_bind]
  all_goals
    congr 1
    funext p
    repeat' split
    all_goals simp_all

variable {ρ : Nat → Nat} {s t : Store H}

theorem repl_self {D : Nat → Prop} (hst : Emb ρ D s t) : repl t.globals t.funcs s = t := by
  cases t
  simp only [repl, hst.tags, hst.mems, hst.tables, hst.datas, hst.elems, hst.structs, hst.arrays,
    hst.exns]

theorem emb_repl {D : Nat → Prop} (hst : Emb ρ D s t) {s' : Store H}
    (hg : s'.globals = s.globals) (hf : s'.funcs = s.funcs) :
    Emb ρ D s' (repl t.globals t.funcs s') where
  globals a ha := by rw [hg]; exact hst.globals a ha
  inj := hst.inj
  funcs := by rw [hf]; exact hst.funcs
  fdom := by rw [hf]; exact hst.fdom
  tags := rfl
  mems := rfl
  tables := rfl
  datas := rfl
  elems := rfl
  structs := rfl
  arrays := rfl
  exns := rfl

theorem global?_repl (hst : Emb ρ Univ s t) (f : Frame) (x : GlobalIdx) :
    ((repl t.globals t.funcs s).global? (frame ρ f) x).map (·.2) = (s.global? f x).map (·.2) := by
  rw [repl_self hst]
  simp only [Store.global?, frame, moduleView, List.getElem?_map, Option.bind_eq_bind]
  cases f.module.globals[x.toNat]? with
  | none => rfl
  | some a =>
    simp only [Option.map_some, Option.bind_some, hst.globals a trivial]
    cases s.globals[a]? <;> rfl

theorem constInstr?_emb (hst : Emb ρ Univ s t) {f : Frame} {vs vs' : List Val} {i : Instr}
    {s' : Store H} (h : constInstr? s f vs i = some (s', vs')) :
    ∃ t', constInstr? t (frame ρ f) vs i = some (t', vs') ∧ Emb ρ Univ s' t' := by
  have he := constInstr?_repl (ρ := ρ) (s := s) (f := f) (vs := vs) (i := i) t.globals t.funcs
    (global?_repl hst f)
  rw [repl_self hst, h] at he
  obtain ⟨hg, hf⟩ := constInstr?_shape h
  exact ⟨_, he, emb_repl hst hg hf⟩

theorem constExpr?_emb {f : Frame} (e : Expr) :
    ∀ {s t : Store H} {vs : List Val} {r : Store H × List Val}, Emb ρ Univ s t →
      e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) (s, vs) = some r →
      ∃ t', e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 (frame ρ f) st.2 i)
        (t, vs) = some (t', r.2) ∧ Emb ρ Univ r.1 t' := by
  induction e with
  | nil =>
    intro s t vs r hst h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hst⟩
  | cons i e ih =>
    intro s t vs r hst h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨s₁, vs₁⟩, h₁, h₂⟩ := h
    obtain ⟨t₁, ht₁, hst₁⟩ := constInstr?_emb hst h₁
    obtain ⟨t', ht', hst'⟩ := ih hst₁ h₂
    refine ⟨t', ?_, hst'⟩
    simp only [List.foldlM_cons, Option.bind_eq_bind, ht₁, Option.bind_some]
    exact ht'

theorem evalConst?_emb (hst : Emb ρ Univ s t) {f : Frame} {e : Expr} {s' : Store H} {v : Val}
    (h : evalConst? s f e = some (s', v)) :
    ∃ t', evalConst? t (frame ρ f) e = some (t', v) ∧ Emb ρ Univ s' t' := by
  unfold evalConst? at h ⊢
  split at h
  · rename_i s₁ w hw
    cases h
    obtain ⟨t', ht', hst'⟩ := constExpr?_emb (f := f) e hst hw
    refine ⟨t', ?_, hst'⟩
    simp only [constExpr?, ht']
  · cases h

/-! ## `$evalglobals`, `$evalexprs` -/

theorem lt_of_emb {ι : Nat → Nat} {s t : Store H} (hst : Emb ι Univ s t) :
    ∀ a, a < s.globals.length → ι a < t.globals.length := by
  intro a ha
  have hs : s.globals[a]?.isSome := by simp [ha]
  rw [← hst.globals a trivial] at hs
  simpa using hs

theorem allocGlobal_globals (hst : Emb ρ Univ s t) (hl : ρ s.globals.length = t.globals.length)
    (g : CGlobalType) (v : Val) (a : Nat) :
    (allocGlobal t g v).1.globals[ρ a]? = (allocGlobal s g v).1.globals[a]? := by
  have hga : t.globals[ρ a]? = s.globals[a]? := hst.globals a trivial
  show (t.globals ++ [(⟨g, v⟩ : GlobalInst)])[ρ a]? = (s.globals ++ [(⟨g, v⟩ : GlobalInst)])[a]?
  rcases Nat.lt_trichotomy a s.globals.length with ha | rfl | ha
  · have ht : ρ a < t.globals.length := lt_of_emb hst a ha
    rw [List.getElem?_append_left ht, List.getElem?_append_left ha, hga]
  · rw [hl, List.getElem?_append_right (le_refl _), List.getElem?_append_right (le_refl _),
      Nat.sub_self, Nat.sub_self]
  · have hne : ρ a ≠ t.globals.length := fun e =>
      absurd (hst.inj _ _ trivial trivial (e.trans hl.symm)) (Nat.ne_of_gt ha)
    have hn : s.globals[a]? = none := List.getElem?_eq_none (Nat.le_of_lt ha)
    have hge : t.globals.length ≤ ρ a := List.getElem?_eq_none_iff.1 (hga.trans hn)
    have h₁ : (t.globals ++ [(⟨g, v⟩ : GlobalInst)]).length ≤ ρ a := by
      simp only [List.length_append, List.length_singleton]; omega
    have h₂ : (s.globals ++ [(⟨g, v⟩ : GlobalInst)]).length ≤ a := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [List.getElem?_eq_none h₁, List.getElem?_eq_none h₂]

theorem allocGlobal_emb (hst : Emb ρ Univ s t) (hl : ρ s.globals.length = t.globals.length)
    (g : CGlobalType) (v : Val) : Emb ρ Univ (allocGlobal s g v).1 (allocGlobal t g v).1 :=
  { hst with globals := fun a _ => allocGlobal_globals hst hl g v a }

theorem evalGlobals?_cons {s : Store H} {f : Frame} {g : CGlobalType} {gs : List CGlobalType}
    {e : Expr} {es : List Expr} {r : Store H × Frame × List Val}
    (h : evalGlobals? evalConst? s f (g :: gs) (e :: es) = some r) :
    ∃ s' v s'' f'' vs', evalConst? s f e = some (s', v) ∧
      evalGlobals? evalConst? (allocGlobal s' g v).1
        { f with module := { f.module with globals := f.module.globals ++ [(allocGlobal s' g v).2] } }
        gs es = some (s'', f'', vs') ∧ r = (s'', f'', v :: vs') := by
  simp only [evalGlobals?] at h
  split at h
  · cases h
  · rename_i s' v he
    split at h
    · cases h
    · rename_i s'' f'' vs' hr
      cases h
      exact ⟨s', v, s'', f'', vs', he, hr, rfl⟩

theorem frame_push {f : Frame} {a b : Nat} (hab : ρ a = b) :
    frame ρ { f with module := { f.module with globals := f.module.globals ++ [a] } } =
      { frame ρ f with module := { (frame ρ f).module with
        globals := (frame ρ f).module.globals ++ [b] } } := by
  simp only [frame, moduleView, List.map_append, List.map_cons, List.map_nil, hab]

theorem evalGlobals?_emb :
    ∀ (gts : List CGlobalType) (es : List Expr) {s t : Store H} {f : Frame}
      {r : Store H × Frame × List Val}, Emb ρ Univ s t →
      (∀ a, s.globals.length ≤ a → ρ a = t.globals.length + (a - s.globals.length)) →
      evalGlobals? evalConst? s f gts es = some r →
      ∃ t', evalGlobals? evalConst? t (frame ρ f) gts es = some (t', frame ρ r.2.1, r.2.2) ∧
        Emb ρ Univ r.1 t'
  | [], [], s, t, f, r, hst, _, h => by
    simp only [evalGlobals?, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hst⟩
  | g :: gs, e :: es, s, t, f, r, hst, hl, h => by
    obtain ⟨s', v, s'', f'', vs', he, hr, rfl⟩ := evalGlobals?_cons h
    obtain ⟨t', ht', hst'⟩ := evalConst?_emb hst he
    have hgs : s'.globals = s.globals := (evalConst?_shape he).1
    have hgt : t'.globals = t.globals := (evalConst?_shape ht').1
    have hlen : ρ s'.globals.length = t'.globals.length := by
      rw [hgs, hgt, hl _ (le_refl _), Nat.sub_self, Nat.add_zero]
    have hst₁ := allocGlobal_emb hst' hlen g v
    have hl₁ : ∀ a, (allocGlobal s' g v).1.globals.length ≤ a →
        ρ a = (allocGlobal t' g v).1.globals.length + (a - (allocGlobal s' g v).1.globals.length) := by
      intro a ha
      simp only [allocGlobal, List.length_append, List.length_singleton, hgs, hgt] at ha ⊢
      rw [hl a (by omega)]
      omega
    obtain ⟨t'', ht'', hst''⟩ := evalGlobals?_emb gs es hst₁ hl₁ hr
    refine ⟨t'', ?_, hst''⟩
    have hf := frame_push (f := f) (ρ := ρ) hlen
    simp only [evalGlobals?, ht']
    rw [show (allocGlobal t' g v).2 = t'.globals.length from rfl, ← hf]
    simp only [show (allocGlobal s' g v).2 = s'.globals.length from rfl] at ht''
    rw [ht'']
  | [], _ :: _, _, _, _, _, _, _, h => by simp [evalGlobals?] at h
  | _ :: _, [], _, _, _, _, _, _, h => by simp [evalGlobals?] at h

theorem evalExprs?_emb :
    ∀ (es : List Expr) {s t : Store H} {f : Frame} {r : Store H × Frame × List Ref},
      Emb ρ Univ s t → evalExprs? evalConst? s f es = some r →
      ∃ t', evalExprs? evalConst? t (frame ρ f) es = some (t', frame ρ r.2.1, r.2.2) ∧
        Emb ρ Univ r.1 t'
  | [], s, t, f, r, hst, h => by
    simp only [evalExprs?, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hst⟩
  | e :: es, s, t, f, r, hst, h => by
    simp only [evalExprs?] at h
    split at h
    · rename_i s₁ x he
      split at h
      · cases h
      · rename_i s'' f'' rs' hr
        cases h
        obtain ⟨t₁, ht₁, hst₁⟩ := evalConst?_emb hst he
        obtain ⟨t'', ht'', hst''⟩ := evalExprs?_emb es hst₁ hr
        refine ⟨t'', ?_, hst''⟩
        simp only [evalExprs?, ht₁, ht'']
    · cases h

theorem evalExprss?_emb :
    ∀ (ess : List (List Expr)) {s t : Store H} {f : Frame}
      {r : Store H × Frame × List (List Ref)},
      Emb ρ Univ s t → evalExprss? evalConst? s f ess = some r →
      ∃ t', evalExprss? evalConst? t (frame ρ f) ess = some (t', frame ρ r.2.1, r.2.2) ∧
        Emb ρ Univ r.1 t'
  | [], s, t, f, r, hst, h => by
    simp only [evalExprss?, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hst⟩
  | es :: ess, s, t, f, r, hst, h => by
    simp only [evalExprss?] at h
    split at h
    · cases h
    · rename_i s₁ f₁ rs he
      split at h
      · cases h
      · rename_i s'' f'' rss' hr
        cases h
        obtain ⟨t₁, ht₁, hst₁⟩ := evalExprs?_emb es hst he
        obtain ⟨t'', ht'', hst''⟩ := evalExprss?_emb ess hst₁ hr
        refine ⟨t'', ?_, hst''⟩
        simp only [evalExprss?, ht₁, ht'']


/-! ## Address maps -/

/-- The global map: `ι` below `n`, then a shift to `N + c`. -/
def shiftMap (ι : Nat → Nat) (n N c : Nat) (a : Nat) : Nat :=
  if a < n then ι a else N + c + (a - n)

theorem shiftMap_lt {ι : Nat → Nat} {n N c a : Nat} (h : a < n) : shiftMap ι n N c a = ι a := by
  simp only [shiftMap, h, ite_true]

theorem shiftMap_ge {ι : Nat → Nat} {n N c a : Nat} (h : n ≤ a) :
    shiftMap ι n N c a = N + c + (a - n) := by
  simp only [shiftMap, Nat.not_lt.2 h, ite_false]

theorem shiftMap_injective {ι : Nat → Nat} {n N : Nat} (c : Nat) (hinj : Function.Injective ι)
    (hlt : ∀ a, a < n → ι a < N) : Function.Injective (shiftMap ι n N c) := by
  intro a b h
  by_cases ha : a < n <;> by_cases hb : b < n
  · rw [shiftMap_lt ha, shiftMap_lt hb] at h
    exact hinj h
  · rw [shiftMap_lt ha, shiftMap_ge (Nat.not_lt.1 hb)] at h
    have := hlt a ha
    omega
  · rw [shiftMap_ge (Nat.not_lt.1 ha), shiftMap_lt hb] at h
    have := hlt b hb
    omega
  · rw [shiftMap_ge (Nat.not_lt.1 ha), shiftMap_ge (Nat.not_lt.1 hb)] at h
    omega

/-- Global lookups after appending `G` once (single allocation) and twice (the spec). -/
theorem globals_twice {α : Type} {ι : Nat → Nat} {S T G : List α}
    (h : ∀ a, T[ι a]? = S[a]?) (a : Nat) :
    (T ++ G ++ G)[shiftMap ι S.length T.length G.length a]? = (S ++ G)[a]? := by
  by_cases ha : a < S.length
  · have hs : S[a]?.isSome := by simp [ha]
    have ht : ι a < T.length := by
      rw [← h a] at hs
      simpa using hs
    rw [shiftMap_lt ha, List.append_assoc, List.getElem?_append_left ht,
      List.getElem?_append_left ha, h a]
  · have hle : (T ++ G).length ≤ T.length + G.length + (a - S.length) := by
      simp only [List.length_append]; omega
    rw [shiftMap_ge (Nat.not_lt.1 ha), List.getElem?_append_right hle,
      List.getElem?_append_right (Nat.not_lt.1 ha)]
    simp only [List.length_append]
    congr 1
    omega

theorem modDom_mono {D D' : Nat → Prop} {m : ModuleInst} (h : ModDom D m) (hD : ∀ a, D a → D' a) :
    ModDom D' m :=
  ⟨fun a ha => hD a (h.1 a ha), fun e he a ha => hD a (h.2 e he a ha)⟩

/-- Renamings agreeing below `n` agree on functions naming globals below `n`. -/
theorem map_function_congr {ρ σ : Nat → Nat} {n : Nat} {l : List (FuncInst H)}
    (hb : ∀ fi ∈ l, ModDom (· < n) fi.module) (h : ∀ a, a < n → ρ a = σ a) :
    l.map (function ρ) = l.map (function σ) := by
  refine List.map_congr_left fun fi hfi => ?_
  simp only [function, moduleView_congr (hb fi hfi) h]

/-! ## Exports -/

/-- Rename the address of an export instance. -/
def exportView (ρ : Nat → Nat) (x : ExportInst) : ExportInst := { x with addr := external ρ x.addr }

theorem allocExport?_view (ρ : Nat → Nat) (mi : ModuleInst) (e : Export) (hx : mi.exports = []) :
    allocExport? (moduleView ρ mi) e = (allocExport? mi e).map (exportView ρ) := by
  have hx' : (moduleView ρ mi).exports = [] := by simp only [moduleView, hx, List.map_nil]
  cases hi : e.index <;>
    simp [allocExport?, hi, moduleView, List.getElem?_map, Option.map_map, Function.comp_def,
      exportView, external]

theorem mapM_option_map {α β γ : Type} (g : α → Option β) (h : β → γ) :
    ∀ l : List α, l.mapM (fun x => (g x).map h) = (l.mapM g).map (List.map h)
  | [] => rfl
  | x :: l => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def]
    cases g x with
    | none => rfl
    | some y =>
      simp only [Option.map_some, Option.bind_some, mapM_option_map g h l]
      cases l.mapM g <;> rfl

theorem mapM_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM g = some l' → ∀ y ∈ l', ∃ x ∈ l, g x = some y
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    intro y hy
    cases hy
  | x :: l, l', h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨y₀, hy₀, l₀, hl₀, rfl⟩ := h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact ⟨x, List.mem_cons_self, hy₀⟩
    · obtain ⟨x', hx', hgx⟩ := mapM_mem hl₀ y hy'
      exact ⟨x', List.mem_cons_of_mem _ hx', hgx⟩

theorem allocExport?_global {mi : ModuleInst} {e : Export} {x : ExportInst} {a : Nat}
    (h : allocExport? mi e = some x) (ha : x.addr = .global a) : a ∈ mi.globals := by
  unfold allocExport? at h
  cases hi : e.index <;>
    simp only [hi, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h <;>
    obtain ⟨b, hb, rfl⟩ := h <;>
    simp only [ExternAddr.global.injEq, reduceCtorEq] at ha
  subst ha
  exact List.mem_of_getElem? hb


/-! ## `$allocmodule` -/

/-- The module instance that `allocModule?` builds before its exports. -/
def exportsInst (s : Store H) (m : Module) (xas : List ExternAddr) (ng nt : Nat)
    (tagTypes : List DefType) : ModuleInst :=
  { tags := ExternAddr.tags xas ++ List.range' s.tags.length tagTypes.length,
    globals := ExternAddr.globals xas ++ List.range' s.globals.length ng,
    mems := ExternAddr.mems xas ++ List.range' s.mems.length m.memories.length,
    tables := ExternAddr.tables xas ++ List.range' s.tables.length nt,
    funcs := ExternAddr.funcs xas ++ (List.range m.funcs.length).map (s.funcs.length + ·) }

/-- The module instance that `allocModule?` returns. -/
def allocInst (s : Store H) (m : Module) (xas : List ExternAddr) (ng nt ne : Nat)
    (tagTypes : List DefType) (xi : List ExportInst) : ModuleInst :=
  { exportsInst s m xas ng nt tagTypes with
    types := allocTypes m.types,
    datas := List.range' s.datas.length m.data.length,
    elems := List.range' s.elems.length ne,
    exports := xi }

/-- The store that `allocModule?` returns. -/
def allocStore (s : Store H) (m : Module) (valsG : List Val) (refsT : List Ref)
    (refsE : List (List Ref)) (tagTypes funcTypes : List DefType) (mi : ModuleInst) :
    Store H :=
  { s with
    tags := s.tags ++ tagTypes.map TagInst.mk,
    globals := s.globals ++
      ((m.globals.map fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
        valsG).map (fun p => ⟨p.1, p.2⟩),
    mems := s.mems ++ m.memories.map fun m =>
      ⟨m, ByteArray.mk (Array.replicate (m.limits.min.val * Execution.Memory.pageSize) 0)⟩,
    tables := s.tables ++
      ((m.tables.map fun t => (⟨t.type.address, t.type.limits,
        (liftRef t.type.element).substAll ((allocTypes m.types).map .dt)⟩ : CTableType)).zip
        refsT).map (fun p => ⟨p.1, List.replicate p.1.limits.min.val p.2⟩),
    datas := s.datas ++ (m.data.map Data.bytes).map DataInst.mk,
    elems := s.elems ++
      ((m.elems.map fun e => (liftRef e.type).substAll ((allocTypes m.types).map .dt)).zip
        refsE).map (fun p => ⟨p.1, p.2⟩),
    funcs := s.funcs ++ (funcTypes.zip m.funcs).map fun p => ⟨p.1, mi, .wasm p.2⟩ }

theorem allocModule?_inv' {s s' : Store H} {m : Module} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)} {mi : ModuleInst}
    (h : allocModule? s m xas valsG refsT refsE = some (s', mi)) :
    ∃ tagTypes funcTypes xi,
      m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes ∧
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes ∧
      m.exports.mapM (allocExport? (exportsInst s m xas (min m.globals.length valsG.length)
        (min m.tables.length refsT.length) tagTypes)) = some xi ∧
      mi = allocInst s m xas (min m.globals.length valsG.length) (min m.tables.length refsT.length)
        (min m.elems.length refsE.length) tagTypes xi ∧
      s' = allocStore s m valsG refsT refsE tagTypes funcTypes mi := by
  obtain ⟨tagTypes, funcTypes, xi, hT, hF, hX, hmi, hs⟩ := allocModule?_inv h
  exact ⟨tagTypes, funcTypes, xi, hT, hF, hX, hmi, hs⟩

theorem allocModule?_of {s : Store H} {m : Module} {xas : List ExternAddr}
    {valsG : List Val} {refsT : List Ref} {refsE : List (List Ref)}
    {tagTypes funcTypes : List DefType} {xi : List ExportInst}
    (hT : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes)
    (hF : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes)
    (hX : m.exports.mapM (allocExport? (exportsInst s m xas (min m.globals.length valsG.length)
        (min m.tables.length refsT.length) tagTypes)) = some xi) :
    allocModule? s m xas valsG refsT refsE =
      some (allocStore s m valsG refsT refsE tagTypes funcTypes
          (allocInst s m xas (min m.globals.length valsG.length)
            (min m.tables.length refsT.length) (min m.elems.length refsE.length) tagTypes xi),
        allocInst s m xas (min m.globals.length valsG.length) (min m.tables.length refsT.length)
          (min m.elems.length refsE.length) tagTypes xi) := by
  unfold allocModule?
  simp only [Option.bind_eq_bind, hT, hF, Option.bind_some, allocMany_tag_eq, allocMany_global_eq,
    allocMany_mem_eq, allocMany_table_eq, allocMany_data_eq, allocMany_elem_eq]
  simp only [exportsInst] at hX
  simp [hX, allocMany_func_eq, allocStore, allocInst, exportsInst, Function.comp_def]


theorem globals_shift {ι : Nat → Nat} (n N k : Nat) :
    ((List.range k).map (n + ·)).map (shiftMap ι n N k) = List.range' (N + k) k := by
  rw [List.map_map, List.range'_eq_map_range]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, shiftMap_ge (Nat.le_add_right n i)]
  omega

/-- The provisional instances of the spec allocation and of the residue's allocation. -/
theorem exportsInst_twice {ρ ι : Nat → Nat} {s₂ t₂ : Store H} (hs2 : Emb ρ Univ s₂ t₂)
    {m : Module} {xas : List ExternAddr} (hxg : ExternAddr.globals xas = []) {n N : Nat}
    (ht2 : t₂.globals.length = N + m.globals.length) (nt : Nat) (tagTypes : List DefType) :
    exportsInst t₂ m xas m.globals.length nt tagTypes =
      moduleView (shiftMap ι n N m.globals.length)
        (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt tagTypes) := by
  have hglob : ((ExternAddr.globals (xas ++ globalAddrs n m.globals.length)) ++
      List.range' s₂.globals.length 0).map (shiftMap ι n N m.globals.length) =
      ExternAddr.globals xas ++ List.range' t₂.globals.length m.globals.length := by
    rw [ExternAddr.globals_append, hxg, ExternAddr.globals_globalAddrs, ht2, List.range'_zero,
      List.append_nil, List.nil_append, List.nil_append, globals_shift]
  simp only [exportsInst, moduleView, hglob, ExternAddr.tags_append, ExternAddr.tags_globalAddrs,
    ExternAddr.mems_append, ExternAddr.mems_globalAddrs, ExternAddr.tables_append,
    ExternAddr.tables_globalAddrs, ExternAddr.funcs_append, ExternAddr.funcs_globalAddrs,
    List.append_nil, hs2.tags, hs2.mems, hs2.tables, hs2.funcs_length, List.map_nil,
    Module.globalResidue]

theorem evalGlobals?_length :
    ∀ (gts : List CGlobalType) (es : List Expr) {s : Store H} {f : Frame}
      {r : Store H × Frame × List Val},
      evalGlobals? evalConst? s f gts es = some r → r.2.2.length = gts.length
  | [], [], s, f, r, h => by
    simp only [evalGlobals?, Option.some.injEq] at h
    subst h
    rfl
  | g :: gs, e :: es, s, f, r, h => by
    obtain ⟨s', v, s'', f'', vs', -, hr, rfl⟩ := evalGlobals?_cons h
    have := evalGlobals?_length gs es hr
    simp only [List.length_cons, this]
  | [], _ :: _, _, _, _, h => by simp [evalGlobals?] at h
  | _ :: _, [], _, _, _, h => by simp [evalGlobals?] at h


theorem allocInst_twice {ρ ι : Nat → Nat} {s₂ t₂ : Store H} (hs2 : Emb ρ Univ s₂ t₂)
    {m : Module} {xas : List ExternAddr} (hxg : ExternAddr.globals xas = []) {n N : Nat}
    (ht2 : t₂.globals.length = N + m.globals.length) (nt ne : Nat) (tagTypes : List DefType)
    (xi : List ExportInst) :
    allocInst t₂ m xas m.globals.length nt ne tagTypes (xi.map (exportView (shiftMap ι n N
        m.globals.length))) =
      moduleView (shiftMap ι n N m.globals.length)
        (allocInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt ne tagTypes
          xi) := by
  have hEI := exportsInst_twice (ι := ι) (n := n) hs2 hxg ht2 nt tagTypes
  unfold allocInst
  rw [hEI]
  simp only [moduleView, hs2.datas, hs2.elems, Module.globalResidue]
  rfl

theorem allocStore_globals {ι : Nat → Nat} {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) {m : Module} {vs : List Val} {rT : List Ref}
    (hG : ((m.globals.map fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
        vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G)
    (tagTypes funcTypes : List DefType) (mi mi' : ModuleInst) (a : Nat) :
    (allocStore t₂ m vs rT [] tagTypes funcTypes mi').globals[shiftMap ι s.globals.length
        t.globals.length G.length a]? =
      (allocStore s₂ m.globalResidue [] rT [] tagTypes funcTypes mi).globals[a]? := by
  have hs4 : (allocStore s₂ m.globalResidue [] rT [] tagTypes funcTypes mi).globals =
      s.globals ++ G := by
    simp only [allocStore, hs2g, List.zip_nil_right, List.map_nil, List.append_nil]
  have ht4 : (allocStore t₂ m vs rT [] tagTypes funcTypes mi').globals = t.globals ++ G ++ G := by
    simp only [allocStore, ht2g, hG]
  rw [hs4, ht4]
  exact globals_twice (fun b => hst.globals b trivial) a

theorem allocStore_funcs {ι ρ : Nat → Nat} {s t s₂ t₂ : Store H}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    (hs2f : s₂.funcs = s.funcs) {m : Module} {vs : List Val} {rT : List Ref} (c : Nat)
    (tagTypes funcTypes : List DefType) (mi : ModuleInst) :
    (allocStore t₂ m vs rT [] tagTypes funcTypes
        (moduleView (shiftMap ι s.globals.length t.globals.length c) mi)).funcs =
      (allocStore s₂ m.globalResidue [] rT [] tagTypes funcTypes mi).funcs.map
        (function (shiftMap ι s.globals.length t.globals.length c)) := by
  have hold : t₂.funcs = s.funcs.map (function (shiftMap ι s.globals.length t.globals.length c)) := by
    rw [hs2.funcs, hs2f]
    refine map_function_congr hb fun a ha => ?_
    rw [hρ a ha, shiftMap_lt ha]
  simp only [allocStore, hold, hs2f, List.map_append, List.map_map]
  rfl

theorem allocStore_emb {ι ρ : Nat → Nat} {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    (hinj : Function.Injective ι) (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) (hs2f : s₂.funcs = s.funcs)
    {m : Module} {vs : List Val} {rT : List Ref}
    (hG : ((m.globals.map fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
        vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G)
    (tagTypes funcTypes : List DefType) (mi : ModuleInst) :
    Emb (shiftMap ι s.globals.length t.globals.length G.length) Univ
      (allocStore s₂ m.globalResidue [] rT [] tagTypes funcTypes mi)
      (allocStore t₂ m vs rT [] tagTypes funcTypes
        (moduleView (shiftMap ι s.globals.length t.globals.length G.length) mi)) :=
  { globals := fun a _ => allocStore_globals hst hs2g ht2g hG tagTypes funcTypes mi _ a
    inj := fun _ _ _ _ h => shiftMap_injective G.length hinj (lt_of_emb hst) h
    funcs := allocStore_funcs hb hs2 hρ hs2f G.length tagTypes funcTypes mi
    fdom := fun fi _ => modDom_univ fi.module
    tags := by simp only [allocStore, hs2.tags]
    mems := by simp only [allocStore, hs2.mems, Module.globalResidue]
    tables := by simp only [allocStore, hs2.tables, Module.globalResidue]
    datas := by simp only [allocStore, hs2.datas, Module.globalResidue]
    elems := by simp only [allocStore, hs2.elems, Module.globalResidue]
    structs := hs2.structs
    arrays := hs2.arrays
    exns := hs2.exns }

theorem allocInst_dom {s₂ : Store H} {m : Module} {xas : List ExternAddr}
    (hxg : ExternAddr.globals xas = []) {n nt ne : Nat} {tagTypes : List DefType}
    {xi : List ExportInst}
    (hX : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs n m.globals.length) 0 nt tagTypes)) = some xi) :
    ModDom (· < n + m.globals.length)
      (allocInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt ne tagTypes
        xi) := by
  have hg : (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt
      tagTypes).globals = (List.range m.globals.length).map (n + ·) := by
    simp only [exportsInst, ExternAddr.globals_append, hxg, ExternAddr.globals_globalAddrs,
      List.range'_zero, List.append_nil, List.nil_append]
  have hlt : ∀ a ∈ (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt
      tagTypes).globals, a < n + m.globals.length := by
    intro a ha
    rw [hg] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have := List.mem_range.1 hi
    omega
  refine ⟨hlt, fun e he a ha => ?_⟩
  obtain ⟨x, -, hx⟩ := mapM_mem hX e he
  exact hlt a (allocExport?_global hx ha)

theorem zip_map_mk (l : List CGlobalType) (vs : List Val) :
    (l.zip vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = List.zipWith GlobalInst.mk l vs := by
  induction l generalizing vs with
  | nil => rfl
  | cons g l ih =>
    cases vs with
    | nil => rfl
    | cons v vs => simp only [List.zip_cons_cons, List.map_cons, List.zipWith_cons_cons, ih]

/-- **`$allocmodule` twice against once.** -/
theorem allocModule?_twice {ι ρ : Nat → Nat} {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    (hinj : Function.Injective ι) (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) (hs2f : s₂.funcs = s.funcs)
    {m : Module} {xas : List ExternAddr} (hxg : ExternAddr.globals xas = []) {vs : List Val}
    {rT : List Ref} (hvs : vs.length = m.globals.length)
    (hG : List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) vs = G)
    {s₄ : Store H} {mi : ModuleInst}
    (hres : allocModule? s₂ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)
      [] rT [] = some (s₄, mi)) :
    ∃ t₄, allocModule? t₂ m xas vs rT [] =
        some (t₄, moduleView (shiftMap ι s.globals.length t.globals.length m.globals.length) mi) ∧
      Emb (shiftMap ι s.globals.length t.globals.length m.globals.length) Univ s₄ t₄ ∧
      ∀ fi ∈ s₄.funcs, ModDom (· < s₄.globals.length) fi.module := by
  obtain ⟨tagTypes, funcTypes, xi, hT, hF, hX, hmi, hs4⟩ := allocModule?_inv' hres
  have hG' : ((m.globals.map fun g => (⟨g.type.mutability,
      (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
      vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G := by
    rw [zip_map_mk]; exact hG
  have hGl : G.length = m.globals.length := by
    rw [← hG, List.length_zipWith, Module.closedGlobalTypes, List.length_map, hvs, Nat.min_self]
  have hk : min m.globals.length vs.length = m.globals.length := by rw [hvs, Nat.min_self]
  have ht2l : t₂.globals.length = t.globals.length + m.globals.length := by
    rw [ht2g, List.length_append, hGl]
  have hX0 : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) 0
      (min m.tables.length rT.length) tagTypes)) = some xi := hX
  have hX' : m.exports.mapM (allocExport? (exportsInst t₂ m xas (min m.globals.length vs.length)
      (min m.tables.length rT.length) tagTypes)) =
      some (xi.map (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length))) := by
    have hv : allocExport? (moduleView (shiftMap ι s.globals.length t.globals.length
        m.globals.length) (exportsInst s₂ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) 0
        (min m.tables.length rT.length) tagTypes)) = fun e => (allocExport? (exportsInst s₂
        m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length) 0
        (min m.tables.length rT.length) tagTypes) e).map
        (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length)) :=
      funext fun e => allocExport?_view _ _ e rfl
    rw [hk, exportsInst_twice (ι := ι) (n := s.globals.length) hs2 hxg ht2l, hv,
      mapM_option_map, hX0]
    rfl
  have hmi' : allocInst t₂ m xas (min m.globals.length vs.length) (min m.tables.length rT.length)
      (min m.elems.length ([] : List (List Ref)).length) tagTypes
      (xi.map (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length))) =
      moduleView (shiftMap ι s.globals.length t.globals.length m.globals.length) mi := by
    rw [hmi, hk, allocInst_twice (ι := ι) (n := s.globals.length) hs2 hxg ht2l]
    rfl
  have hT' : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes := hT
  have hF' : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes := hF
  refine ⟨_, by rw [allocModule?_of hT' hF' hX', hmi'], ?_, ?_⟩
  · have he := allocStore_emb (rT := rT) hst hinj hb hs2 hρ hs2g ht2g hs2f hG' tagTypes funcTypes mi
    rw [hGl] at he
    rw [hs4]
    exact he
  · show ∀ fi ∈ s₄.funcs, ModDom (· < s₄.globals.length) fi.module
    have hdom := allocInst_dom (ne := min m.elems.length 0) hxg hX0
    have hlen : s₄.globals.length = s.globals.length + m.globals.length := by
      rw [hs4]
      simp only [allocStore, hs2g, List.zip_nil_right, List.map_nil, List.append_nil,
        List.length_append, hGl]
    intro fi hfi
    rw [hlen]
    rw [hs4] at hfi
    simp only [allocStore, hs2f, List.mem_append, List.mem_map] at hfi
    rcases hfi with hold | ⟨p, -, rfl⟩
    · exact modDom_mono (hb fi hold) fun a ha => by omega
    · rw [hmi]
      exact hdom


/-! ## `prepare?` -/

theorem prepare?_residue {m : Module} (hseg : m.data = [] ∧ m.elems = []) {s₁ : Store H}
    {xas : List ExternAddr} {c : Config H} {st : Option FuncIdx}
    (h : prepare? evalConst? s₁ m.globalResidue xas = some (c, st)) :
    ∃ s₂ f₂ rT s₄ mi,
      evalExprs? evalConst? s₁ ⟨[], ModuleInst.initial s₁ m.globalResidue xas⟩
        (m.tables.map Table.init) = some (s₂, f₂, rT) ∧
      allocModule? s₂ m.globalResidue xas [] rT [] = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi }, []⟩ ∧ st = m.start := by
  have hst := prepare?_start h
  have hcode := prepare?_code h
  unfold prepare? at h
  split at h
  · simp only [Module.globalResidue_globals, List.map_nil, evalGlobals?] at h
    split at h
    · cases h
    · rename_i s₂ f₂ rT hT
      have hE : m.globalResidue.elems = [] := hseg.2
      simp only [hE, List.map_nil, evalExprss?] at h
      split at h
      · cases h
      · rename_i s₄ mi hM
        cases h
        have hD : m.globalResidue.data = [] := hseg.1
        refine ⟨s₂, f₂, rT, s₄, mi, hT, hM, ?_, hst⟩
        simp only [hD, List.length_nil, List.range_zero, List.zip_nil_right, List.flatMap_nil,
          expression, List.map_nil, List.append_nil]
  · cases h

theorem once_inv {s : Store H} {m : Module} {xas : List ExternAddr}
    (hseg : m.data = [] ∧ m.elems = []) {s' : Store H} {f' : Frame} {st : Option FuncIdx}
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ s₁ f₁ vs s₂ f₂ rT mi,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      evalExprs? evalConst? s₁ f₁ (m.tables.map Table.init) = some (s₂, f₂, rT) ∧
      allocModule? s₂ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)
        [] rT [] = some (s', mi) ∧ f' = { module := mi } ∧ st = m.start := by
  unfold instantiateOnce? at ho
  split at ho
  · cases ho
  · rename_i s₁ f₁ vs hg
    have hf₁ := evalGlobals?_initial hg
    unfold instantiateDirect? prepareDirect? at ho
    split at ho
    · cases ho
    · rename_i c st₀ hp
      obtain ⟨s₂, f₂, rT, s₄, mi, hT, hM, rfl, rfl⟩ := prepare?_residue hseg hp
      have hE : m.globalResidue.elems = [] := hseg.2
      have hD : m.globalResidue.data = [] := hseg.1
      simp only [initSegments?, initElem?, initData?, hE, hD, List.length_nil, List.range_zero,
        List.zip_nil_right, initElemList?, initDataList?, Option.map_some,
        Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl, rfl⟩ := ho
      rw [← hf₁] at hT
      exact ⟨s₁, f₁, vs, s₂, f₂, rT, mi, hg, hT, hM, rfl, rfl⟩

theorem prepare?_of {t : Store H} {m : Module} {xas : List ExternAddr}
    (hseg : m.data = [] ∧ m.elems = []) {t₁ t₂ t₄ : Store H} {g₁ g₂ : Frame} {vs : List Val}
    {rT : List Ref} {mi : ModuleInst}
    (h1 : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (t₁, g₁, vs))
    (h2 : evalExprs? evalConst? t₁ g₁ (m.tables.map Table.init) = some (t₂, g₂, rT))
    (h4 : allocModule? t₂ m xas vs rT [] = some (t₄, mi)) :
    prepare? evalConst? t m xas = some (⟨t₄, { module := mi }, []⟩, m.start) := by
  have hguard : m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
      (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32) := by
    simp only [hseg, List.length_nil, Nat.zero_le, List.not_mem_nil, false_imp_iff, imp_true_iff,
      and_self]
  have h1' : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
      (m.globals.map Global.init) = some (t₁, g₁, vs) := h1
  unfold prepare?
  split
  · simp only [h1', h2, hseg, List.map_nil, evalExprss?, h4, List.length_nil, List.range_zero,
      List.zip_nil_right, List.flatMap_nil, expression, List.append_nil]
  · exact absurd hguard ‹_›

/-! ## The main comparison -/

theorem emb_shift {ι : Nat → Nat} {s t : Store H} (hst : Emb ι Univ s t)
    (hinj : Function.Injective ι) (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (c : Nat) : Emb (shiftMap ι s.globals.length t.globals.length c) Univ s t where
  globals a _ := by
    by_cases ha : a < s.globals.length
    · rw [shiftMap_lt ha]; exact hst.globals a trivial
    · rw [shiftMap_ge (Nat.not_lt.1 ha), List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (Nat.not_lt.1 ha)]
  inj a b _ _ h := shiftMap_injective c hinj (lt_of_emb hst) h
  funcs := by
    rw [hst.funcs]
    exact map_function_congr hb fun a ha => (shiftMap_lt ha).symm
  fdom fi _ := modDom_univ fi.module
  tags := hst.tags
  mems := hst.mems
  tables := hst.tables
  datas := hst.datas
  elems := hst.elems
  structs := hst.structs
  arrays := hst.arrays
  exns := hst.exns

theorem frame_initial {ρ : Nat → Nat} {s t : Store H} {D : Nat → Prop} (hst : Emb ρ D s t)
    {m : Module} {xas : List ExternAddr} (hxg : ExternAddr.globals xas = []) :
    frame ρ ⟨[], ModuleInst.initial s m xas⟩ = ⟨[], ModuleInst.initial t m xas⟩ := by
  simp only [frame, moduleView, ModuleInst.initial, hxg, List.map_nil, hst.funcs_length]

/-- Spec preparation (`prepare?`, globals allocated twice) against single allocation
(`instantiateOnce?`) on embedded stores, for modules without data/element segments and without
global imports. -/
theorem prepare_once {s t : Store H} {ι : Nat → Nat}
    (hst : Emb ι Univ s t) (hinj : Function.Injective ι)
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr} (hxg : ExternAddr.globals xas = [])
    (hseg : m.data = [] ∧ m.elems = [])
    {s' : Store H} {f' : Frame} {st : Option FuncIdx}
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ (c : Config H) (ι' : Nat → Nat),
      prepare? evalConst? t m xas = some (c, st) ∧
      c.code = [] ∧ Function.Injective ι' ∧ Emb ι' Univ s' c.store ∧
      c.frame = frame ι' f' ∧ (∀ a, a < s.globals.length → ι' a = ι a) ∧
      ∀ fi ∈ s'.funcs, ModDom (· < s'.globals.length) fi.module := by
  obtain ⟨s₁, f₁, vs, s₂, f₂, rT, mi, hg, hT, hM, rfl, rfl⟩ := once_inv hseg ho
  have hρ : Emb (shiftMap ι s.globals.length t.globals.length 0) Univ s t :=
    emb_shift hst hinj hb 0
  have hl : ∀ a, s.globals.length ≤ a → shiftMap ι s.globals.length t.globals.length 0 a =
      t.globals.length + (a - s.globals.length) := fun a ha => by
    rw [shiftMap_ge ha, Nat.add_zero]
  obtain ⟨t₁, ht₁, hst₁⟩ := evalGlobals?_emb _ _ hρ hl hg
  obtain ⟨t₂, ht₂, hst₂⟩ := evalExprs?_emb _ hst₁ hT
  have ht₁' : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m xas⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) =
      some (t₁, frame (shiftMap ι s.globals.length t.globals.length 0) f₁, vs) := by
    rw [← frame_initial hρ hxg]; exact ht₁
  obtain ⟨hs1g, hs1f, -⟩ := evalGlobals?_shape hg
  obtain ⟨ht1g, -, -⟩ := evalGlobals?_shape ht₁'
  obtain ⟨hs2g, hs2f, -⟩ := evalExprs?_shape hT
  obtain ⟨ht2g, -, -⟩ := evalExprs?_shape ht₂
  have hvs : vs.length = m.globals.length := by
    rw [evalGlobals?_length _ _ hg, Module.closedGlobalTypes, List.length_map]
  have hag : ∀ a, a < s.globals.length →
      shiftMap ι s.globals.length t.globals.length 0 a = ι a := fun a ha => shiftMap_lt ha
  obtain ⟨t₄, ht₄, hst₄, hbd⟩ := allocModule?_twice hst hinj hb hst₂ hag
    (hs2g.trans hs1g) (ht2g.trans ht1g) (hs2f.trans hs1f) hxg hvs rfl hM
  refine ⟨⟨t₄, { module := moduleView (shiftMap ι s.globals.length t.globals.length
      m.globals.length) mi }, []⟩, shiftMap ι s.globals.length t.globals.length m.globals.length,
    prepare?_of hseg ht₁' ht₂ ht₄, rfl,
    shiftMap_injective _ hinj (lt_of_emb hst), hst₄, rfl, fun a ha => shiftMap_lt ha, hbd⟩

end Silmaril.Proofs.Wasm.Models.V2CoreSpecH
