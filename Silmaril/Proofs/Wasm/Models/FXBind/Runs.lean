module

public import Silmaril.Proofs.Wasm.Models.FXBind.Inv

/-!
# Partial application: the runs of the source

With `S = vs₂ ++ vs₁` the source's operand stack, `d` the type of `a`, and no host calls:

* `bsrc_succ₁`: the only successor of the source is `bsrc₁` (`cont.new`);
* `bsrc_succ₂`: the successors of `bsrc₁` are `bsrc₂ U₁ U₂` for the splits `S = U₁ ++ U₂`
  (`cont.bind` binds `U₂`);
* `bsrc_succ₃`: the successors of `bsrc₂ U₁ U₂` are, for the splits `U₁ = X₁ ++ X₂`, the call
  `U₂ ++ X₂; ref.func a; call_ref` under a handler frame after the values `X₁`;
* `bsrc_runs` (any host): for every split `S = X₂ ++ U₂` the source reaches the call on the
  rotation `U₂ ++ X₂` under a handler frame.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXBind

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXBind
open Silmaril.Wasm.Models.FXLower (tgtCall onHandler)
open Silmaril.Proofs.Wasm.Models.FXLower (seq_split no_step_cvals cvals_append_cons_inj
  core_ne_cvals_cons cvals_append contOf kAfter plug_contOf step_contNew step_resume underH
  underHW cons_not_result)
open Silmaril.Wasm.SingleThreaded.Det (noHost append_singleton_inj)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- The continuation store after `cont.bind` bound `U`. -/
def kBind (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) (U : List Val) :
    List (Option ContFX) :=
  kAfter K a d ++ [some (bindK (contOf a d) U)]

/-- The continuation store after `resume` consumed the bound continuation. -/
def kRes (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) (U : List Val) :
    List (Option ContFX) :=
  (kBind K a d U).set (K.length + 1) none

/-- The source after `cont.new`. -/
def bsrc₁ (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat) (d : Validation.DefType)
    (ct ct' : TypeIdx) (hs : List OnClause) (S : List Val) : ConfigFX H :=
  ⟨s, K ++ [some (contOf a d)], f,
    cvals S ++ .contRef K.length :: [.fx (.contBind ct ct'), .fx (.resume ct' hs)]⟩

/-- The source after `cont.bind` bound `U₂` and left `U₁`. -/
def bsrc₂ (s : Store H) (K : List (Option ContFX)) (f : Frame) (a : Nat) (d : Validation.DefType)
    (ct' : TypeIdx) (hs : List OnClause) (U₁ U₂ : List Val) : ConfigFX H :=
  ⟨s, kBind K a d U₂, f, cvals U₁ ++ .contRef (K.length + 1) :: [.fx (.resume ct' hs)]⟩

theorem srcBind_eq (a : Nat) (ct ct' : TypeIdx) (hs : List OnClause) (vs₂ vs₁ : List Val) :
    srcBind a ct ct' hs vs₂ vs₁ = cvals (vs₂ ++ vs₁ ++ [.ref (.func a)]) ++
      .fx (.contNew ct) :: [.fx (.contBind ct ct'), .fx (.resume ct' hs)] := by
  simp only [srcBind, cvals_append, List.append_assoc]
  rfl

theorem kAfter_length (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) :
    (kAfter K a d).length = K.length + 1 := by
  simp [kAfter]

theorem kOne_get (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) :
    (K ++ [some (contOf a d)])[K.length]? = some (some (contOf a d)) := by
  simp

theorem kBind_get (K : List (Option ContFX)) (a : Nat) (d : Validation.DefType) (U : List Val) :
    (kBind K a d U)[K.length + 1]? = some (some (bindK (contOf a d) U)) := by
  rw [kBind, ← kAfter_length K a d]
  simp

/-- The bound continuation plugged with `X` is the call on `U ++ X`. -/
theorem plug_bindK (a : Nat) (d : Validation.DefType) (U X : List Val) :
    (bindK (contOf a d) U).plug (cvals X) = (tgtCall a d (U ++ X)).map .core := by
  show (contOf a d).plug (cvals U ++ cvals X) = _
  rw [← cvals_append, plug_contOf]

/-- **The only successor of the source is `bsrc₁`.** -/
theorem bsrc_succ₁ {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {fi : FuncInst H} {ct ct' : TypeIdx} {hs : List OnClause} {vs₂ vs₁ : List Val}
    (hf : s.funcs[a]? = some fi) {y : ConfigFX H}
    (h : StepFX P noHost noFX ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩ y) :
    y = bsrc₁ s K f a fi.type ct ct' hs (vs₂ ++ vs₁) := by
  obtain ⟨W₀, r, hW, hy⟩ := step_contNew h _ ct _ (srcBind_eq a ct ct' hs vs₂ vs₁)
  obtain ⟨rfl, hr⟩ := append_singleton_inj.mp hW
  have hr' : r = .func a := by simpa using hr.symm
  rcases hy with ⟨a', fi', ha, hf', rfl⟩ | ⟨hn, -⟩
  · have ha' : a' = a := by simpa [hr'] using ha.symm
    have hfi : fi' = fi := by rw [ha'] at hf'; exact Option.some.inj (hf'.symm.trans hf)
    rw [ha', hfi]
    rfl
  · exact absurd (hr'.symm.trans hn) (by simp)

/-- **The successors of `bsrc₁`: `cont.bind` with every split of the stack.** -/
theorem bsrc_succ₂ {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct ct' : TypeIdx} {hs : List OnClause} {S : List Val}
    {y : ConfigFX H} (h : StepFX P noHost noFX (bsrc₁ s K f a d ct ct' hs S) y) :
    ∃ U₁ U₂, S = U₁ ++ U₂ ∧ y = bsrc₂ s K f a d ct' hs U₁ U₂ := by
  obtain ⟨T', hT, U₁, U₂, rfl, hy⟩ :=
    step_contBind h S K.length ct ct' _ (Or.inr rfl) rfl
  have hT' : T' = [.fx (.resume ct' hs)] := (List.cons.inj hT).2.symm
  subst hT'
  rcases hy with ⟨C, hk, rfl⟩ | ⟨hk, -⟩
  · have hC : C = contOf a d := by
      have h1 := (kOne_get K a d).symm.trans hk
      simpa using h1.symm
    subst hC
    refine ⟨U₁, U₂, rfl, ?_⟩
    simp [bsrc₁, bsrc₂, kBind, kAfter]
  · exact absurd ((kOne_get K a d).symm.trans hk) (by simp)

/-- **The successors of `bsrc₂`: the call on `U₂ ++ X₂` after the values `X₁`.** -/
theorem bsrc_succ₃ {s : Store H} {K : List (Option ContFX)} {f : Frame} {a : Nat}
    {d : Validation.DefType} {ct' : TypeIdx} {hs : List OnClause} {U₁ U₂ : List Val}
    {y : ConfigFX H} (h : StepFX P noHost noFX (bsrc₂ s K f a d ct' hs U₁ U₂) y) :
    ∃ hs' X₁ X₂, U₁ = X₁ ++ X₂ ∧
      y = underHW (kRes K a d U₂) hs' X₁ ⟨s, f, tgtCall a d (U₂ ++ X₂)⟩ := by
  obtain ⟨T', hT, X₁, X₂, rfl, hy⟩ :=
    step_resume h U₁ (K.length + 1) ct' hs _ (Or.inr rfl) rfl
  have hT' : T' = [] := (List.cons.inj hT).2.symm
  subst hT'
  rcases hy with ⟨C, hs', hk, -, rfl⟩ | ⟨hk, -⟩
  · have hC : C = bindK (contOf a d) U₂ := by
      have h1 := (kBind_get K a d U₂).symm.trans hk
      simpa using h1.symm
    subst hC
    refine ⟨hs', X₁, X₂, rfl, ?_⟩
    show _ = (⟨s, kRes K a d U₂, f,
      cvals X₁ ++ [.handler hs' ((tgtCall a d (U₂ ++ X₂)).map .core)]⟩ : ConfigFX H)
    rw [← plug_bindK]
    rfl
  · exact absurd ((kBind_get K a d U₂).symm.trans hk) (by simp)

/-- **The source reaches every rotation** (any host, any FX table): for `S = X₂ ++ U₂`, binding
`U₂` and resuming with `X₂` runs the call on `U₂ ++ X₂` under the handler frame. -/
theorem bsrc_runs {host : HostSemantics H} {fx : H → Option FuncFX} {s : Store H}
    {K : List (Option ContFX)} {f : Frame} {a : Nat} {fi : FuncInst H} {ct ct' : TypeIdx}
    {hs : List OnClause} {hs' : List HClause} {vs₂ vs₁ X₂ U₂ : List Val}
    (hf : s.funcs[a]? = some fi) (hr : hs.mapM (resolve s f) = some hs')
    (hS : vs₂ ++ vs₁ = X₂ ++ U₂) :
    StepsFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩
      (underH (kRes K a fi.type U₂) hs' ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩) := by
  have h1 : StepFX P host fx ⟨s, K, f, srcBind a ct ct' hs vs₂ vs₁⟩
      (bsrc₁ s K f a fi.type ct ct' hs (X₂ ++ U₂)) := by
    have h := StepFX.seq (vs := X₂ ++ U₂) (rest := [.fx (.contBind ct ct'), .fx (.resume ct' hs)])
      (StepFX.contNew (P := P) (host := host) (fx := fx) (K := K) (f := f) (ct := ct) hf)
      (Or.inr (by simp))
    simpa [srcBind, bsrc₁, contOf, hS] using h
  have h2 : StepFX P host fx (bsrc₁ s K f a fi.type ct ct' hs (X₂ ++ U₂))
      (bsrc₂ s K f a fi.type ct' hs X₂ U₂) := by
    have h := StepFX.seq (vs := X₂) (rest := [.fx (.resume ct' hs)])
      (StepFX.contBind (P := P) (host := host) (fx := fx) (s := s) (f := f) (vs := U₂)
        (ct := ct) (ct' := ct') (kOne_get K a fi.type))
      (Or.inr (by simp))
    simpa [bsrc₁, bsrc₂, kBind, kAfter, bindK] using h
  have h3 : StepFX P host fx (bsrc₂ s K f a fi.type ct' hs X₂ U₂)
      (underH (kRes K a fi.type U₂) hs' ⟨s, f, tgtCall a fi.type (U₂ ++ X₂)⟩) := by
    have h := StepFX.resume (P := P) (host := host) (fx := fx) (s := s) (f := f) (vs := X₂)
      (ct := ct') (kBind_get K a fi.type U₂) hr
    unfold underH onHandler kRes
    rw [← plug_bindK]
    exact h
  exact ((Relation.ReflTransGen.single h1).tail h2).tail h3

end Silmaril.Proofs.Wasm.Models.FXBind
