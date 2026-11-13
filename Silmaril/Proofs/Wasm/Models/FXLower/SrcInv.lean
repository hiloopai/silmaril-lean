module

public import Silmaril.Proofs.Wasm.Models.FXLower.Fnv
public import Silmaril.Proofs.Wasm.Models.FXLower.Lower

/-!
# Inverting the steps of the lowering's source (no host calls)

Three step inversions, each by induction on `StepFX`, using the first non-value `fnvX`: the
`seq` rule reduces to the induction hypothesis (`seq_split`), and every rule whose left-hand side
has a different first non-value is refuted by comparing `fnvX` of both sides.

* `step_contNew`: a step of `cvals W ++ cont.new :: T` is `cont.new` (or `cont.new` of a null
  reference) on the last value of `W`, under `ctxt-instrs`;
* `step_resume`: a step of `cvals W ++ ref.cont n :: resume :: T` is `resume` (or a trap on a
  consumed continuation) with *some* split `W = W₁ ++ W₂`: `W₂` is passed to the continuation,
  `W₁` stays outside the handler frame. The reduction is untyped, so every split occurs;
* `step_prefixHandler`: a step of `cvals W ++ [handler hs X]` is a step of the handler frame,
  with `cvals W` kept in front.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLower

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXLower
open Silmaril.Proofs.Wasm.Models.FX (isCore all_isCore_map all_isCore_cvals)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- FX code with a non-Core instruction after values is not Core code. -/
theorem core_ne_cvals_cons {cs : List Admin} {W : List Val} {e : AdminFX} {T : List AdminFX}
    (he : isCore e = false) : cs.map .core ≠ cvals W ++ e :: T := by
  intro h
  have h1 : (cs.map AdminFX.core).all isCore = true := all_isCore_map cs
  have h2 : (cvals W ++ e :: T).all isCore = false := by simp [he]
  rw [h] at h1
  exact Bool.false_ne_true (h2.symm.trans h1)

/-- The `invoke` rule has a call instruction, not `e`, as its first non-value. -/
theorem invoke_ne {c : Admin} (hc : c.IsCallRef) {vs W : List Val} {a : Nat} {e : AdminFX}
    {T : List AdminFX} (he : ∀ c', e ≠ .core c') :
    cvals vs ++ [.core (.ref (.func a)), .core c] ≠ cvals W ++ e :: T := by
  intro h
  have h' : cvals (vs ++ [.ref (.func a)]) ++ .core c :: [] = cvals W ++ e :: T := by
    rw [← h, cvals_append, List.append_assoc]
    rfl
  obtain ⟨-, hce, -⟩ := cvals_append_cons_inj h' (IsCallRef.val?_none hc) (by
    cases e <;> first | rfl | exact absurd rfl (he _))
  exact he c hce.symm

/-! ## `cont.new` -/

/-- The outcomes of a step of `cvals W ++ cont.new :: T`. -/
def NewRes (s : Store H) (K : List (Option ContFX)) (f : Frame) (W : List Val)
    (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ W₀ r, W = W₀ ++ [.ref r] ∧
    ((∃ a fi, r = .func a ∧ s.funcs[a]? = some fi ∧
        y = ⟨s, K ++ [some (contOf a fi.type)], f, cvals W₀ ++ .contRef K.length :: T⟩) ∨
      (r = .null ∧ y = ⟨s, K, f, cvals W₀ ++ .core .trap :: T⟩))

/-- `NewRes` is closed under `ctxt-instrs`. -/
theorem newRes_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {W : List Val} {T es' : List AdminFX} (vs : List Val) (rest : List AdminFX)
    (h : NewRes s K f W T ⟨s', K', f', es'⟩) :
    NewRes s K f (vs ++ W) (T ++ rest) ⟨s', K', f', cvals vs ++ es' ++ rest⟩ := by
  obtain ⟨W₀, r, rfl, h⟩ := h
  refine ⟨vs ++ W₀, r, by simp, ?_⟩
  rcases h with ⟨a, fi, hr, hf, hy⟩ | ⟨hr, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨a, fi, hr, hf, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hr, by simp⟩

/-- **Inversion at `cont.new`.** -/
theorem step_contNew {x y : ConfigFX H} (h : StepFX P noHost fx x y) :
    ∀ W ct T, x.code = cvals W ++ .fx (.contNew ct) :: T →
      NewRes x.store x.conts x.frame W T y := by
  induction h with
  | core _ => exact fun W ct T hx => absurd hx (core_ne_cvals_cons rfl)
  | seq h _ ih =>
    intro W ct T hx
    rcases seq_split rfl hx with ⟨V, hV⟩ | ⟨W₂, T₁, rfl, hes, rfl⟩
    · exact (no_step_cvals h V hV).elim
    · exact newRes_seq _ _ (ih W₂ ct T₁ hes)
  | @contNew s K f a fi _ hf =>
    intro W ct T hx
    obtain ⟨hW, -, hT⟩ := cvals_append_cons_inj (W₁ := [.ref (.func a)]) (T₁ := []) hx rfl rfl
    exact ⟨[], .func a, hW.symm, Or.inl ⟨a, fi, rfl, hf, by rw [← hT]; rfl⟩⟩
  | contNewNull =>
    intro W ct T hx
    obtain ⟨hW, -, hT⟩ := cvals_append_cons_inj (W₁ := [.ref .null]) (T₁ := []) hx rfl rfl
    exact ⟨[], .null, hW.symm, Or.inr ⟨rfl, by rw [← hT]; rfl⟩⟩
  | invoke hc => exact fun W ct T hx => absurd hx (invoke_ne hc (by simp))
  | _ => intro W ct T hx; fnvX_absurd hx

/-! ## `resume` -/

/-- The outcomes of a step of `cvals W ++ ref.cont n :: T` where `T` starts with `resume`. -/
def ResumeRes (s : Store H) (K : List (Option ContFX)) (f : Frame) (ct : TypeIdx)
    (hs : List OnClause) (W : List Val) (n : Nat) (T : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ T', T = .fx (.resume ct hs) :: T' ∧ ∃ W₁ W₂, W = W₁ ++ W₂ ∧
    ((∃ C hs', K[n]? = some (some C) ∧ hs.mapM (resolve s f) = some hs' ∧
        y = ⟨s, K.set n none, f, cvals W₁ ++ .handler hs' (C.plug (cvals W₂)) :: T'⟩) ∨
      (K[n]? = some none ∧ y = ⟨s, K, f, cvals W₁ ++ .core .trap :: T'⟩))

/-- `ResumeRes` is closed under `ctxt-instrs`. -/
theorem resumeRes_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {ct : TypeIdx} {hs : List OnClause} {W : List Val} {n : Nat} {T es' : List AdminFX}
    (vs : List Val) (rest : List AdminFX) (h : ResumeRes s K f ct hs W n T ⟨s', K', f', es'⟩) :
    ResumeRes s K f ct hs (vs ++ W) n (T ++ rest) ⟨s', K', f', cvals vs ++ es' ++ rest⟩ := by
  obtain ⟨T', rfl, W₁, W₂, rfl, h⟩ := h
  refine ⟨T' ++ rest, rfl, vs ++ W₁, W₂, by simp, ?_⟩
  rcases h with ⟨C, hs', hk, hr, hy⟩ | ⟨hk, hy⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inl ⟨C, hs', hk, hr, by simp⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact Or.inr ⟨hk, by simp⟩

/-- The head condition of `step_resume`. -/
abbrev HeadResume (ct : TypeIdx) (hs : List OnClause) (T : List AdminFX) : Prop :=
  T.head? = none ∨ T.head? = some (.fx (.resume ct hs))

theorem headResume_prefix {ct : TypeIdx} {hs : List OnClause} {T₁ rest : List AdminFX}
    (h : HeadResume ct hs (T₁ ++ rest)) : HeadResume ct hs T₁ := by
  cases T₁ with
  | nil => exact Or.inl rfl
  | cons a T₁ => simpa [HeadResume] using h

/-- A one-instruction tail other than `resume ct hs` fails the head condition. -/
theorem headResume_single {ct ct' : TypeIdx} {hs hs' : List OnClause} {i : FXInstr}
    (h : HeadResume ct hs [.fx i]) (hi : i = .resume ct' hs') : ct' = ct ∧ hs' = hs := by
  subst hi
  simpa [HeadResume] using h

/-- The `resume` and `resumeUsed` cases: the rule's operands are `W`. -/
theorem resume_inj {vs W : List Val} {k n : Nat} {ct ct' : TypeIdx} {hs hs₀ : List OnClause}
    {T : List AdminFX} (hT : HeadResume ct hs T)
    (hx : cvals vs ++ [.contRef k, .fx (.resume ct' hs₀)] = cvals W ++ .contRef n :: T) :
    vs = W ∧ k = n ∧ ct' = ct ∧ hs₀ = hs ∧ T = [.fx (.resume ct hs)] := by
  obtain ⟨hW, hk, hT'⟩ := cvals_append_cons_inj hx rfl rfl
  have hk' : k = n := by simpa using hk
  obtain ⟨rfl, rfl⟩ := headResume_single (hT'.symm ▸ hT) rfl
  exact ⟨hW, hk', rfl, rfl, hT'.symm⟩

/-- The other rules on `ref.cont`: the next instruction is not `resume`. -/
theorem contRef_other {vs W : List Val} {k n : Nat} {ct : TypeIdx} {hs : List OnClause}
    {T : List AdminFX} {i : FXInstr} (hT : HeadResume ct hs T)
    (hi : ∀ ct' hs', i ≠ .resume ct' hs')
    (hx : cvals vs ++ [.contRef k, .fx i] = cvals W ++ .contRef n :: T) : False := by
  obtain ⟨-, -, hT'⟩ := cvals_append_cons_inj hx rfl rfl
  have h1 : HeadResume ct hs [.fx i] := hT'.symm ▸ hT
  rcases h1 with h1 | h1
  · exact absurd h1 (by simp)
  · exact hi ct hs (by simpa using h1)

/-- **Inversion at `resume`.** -/
theorem step_resume {x y : ConfigFX H} (h : StepFX P noHost fx x y) :
    ∀ W n ct hs T, HeadResume ct hs T → x.code = cvals W ++ .contRef n :: T →
      ResumeRes x.store x.conts x.frame ct hs W n T y := by
  induction h with
  | core _ => exact fun W n ct hs T _ hx => absurd hx (core_ne_cvals_cons rfl)
  | seq h _ ih =>
    intro W n ct hs T hT hx
    rcases seq_split rfl hx with ⟨V, hV⟩ | ⟨W₂, T₁, rfl, hes, rfl⟩
    · exact (no_step_cvals h V hV).elim
    · exact resumeRes_seq _ _ (ih W₂ n ct hs T₁ (headResume_prefix hT) hes)
  | @resume s K f vs k C _ _ hs' hk hr =>
    intro W n ct hs T hT hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj hT hx
    exact ⟨[], rfl, [], vs, rfl, Or.inl ⟨C, hs', hk, hr, rfl⟩⟩
  | @resumeUsed s K f vs k _ _ hk =>
    intro W n ct hs T hT hx
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := resume_inj hT hx
    exact ⟨[], rfl, [], vs, rfl, Or.inr ⟨hk, rfl⟩⟩
  | contBind | contBindUsed | resumeThrow =>
    exact fun W n ct hs T hT hx => (contRef_other hT (by simp) hx).elim
  | invoke hc => exact fun W n ct hs T _ hx => absurd hx (invoke_ne hc (by simp))
  | _ => intro W n ct hs T _ hx; fnvX_absurd hx

/-! ## Values in front of a handler frame -/

/-- A one-instruction code is not `cvals W ++ [e]` with `W` non-empty. -/
theorem single_ne {a e : AdminFX} {W : List Val} (hW : W ≠ []) : [a] ≠ cvals W ++ [e] := by
  intro h
  have h1 : [a].length = (cvals W ++ [e]).length := congrArg List.length h
  have h2 : W.length = 0 := by simpa [cvals] using h1
  exact hW (List.length_eq_zero_iff.mp h2)

/-- The outcome of `step_prefixHandler`. -/
abbrev PrefixRes (s : Store H) (K : List (Option ContFX)) (f : Frame) (W : List Val)
    (hs : List HClause) (X : List AdminFX) (y : ConfigFX H) : Prop :=
  ∃ y', StepFX P noHost fx ⟨s, K, f, [.handler hs X]⟩ y' ∧
    y = ⟨y'.store, y'.conts, y'.frame, cvals W ++ y'.code⟩

/-- The `seq` case of `step_prefixHandler`. -/
theorem prefixRes_seq {s s' : Store H} {K K' : List (Option ContFX)} {f f' : Frame}
    {vs W₂ : List Val} {hs : List HClause} {X es' : List AdminFX}
    (h : StepFX P noHost fx ⟨s, K, f, cvals W₂ ++ [.handler hs X]⟩ ⟨s', K', f', es'⟩)
    (ih : W₂ ≠ [] → PrefixRes (P := P) (fx := fx) s K f W₂ hs X ⟨s', K', f', es'⟩) :
    PrefixRes (P := P) (fx := fx) s K f (vs ++ W₂) hs X ⟨s', K', f', cvals vs ++ es' ++ []⟩ := by
  by_cases hW : W₂ = []
  · subst hW
    exact ⟨⟨s', K', f', es'⟩, h, by simp⟩
  · obtain ⟨y', hy', hy⟩ := ih hW
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConfigFX.mk.inj hy
    exact ⟨y', hy', by simp⟩

/-- **Values in front of a handler frame stay in front.** -/
theorem step_prefixHandler {x y : ConfigFX H} (h : StepFX P noHost fx x y) :
    ∀ W hs X, W ≠ [] → x.code = cvals W ++ [.handler hs X] →
      PrefixRes (P := P) (fx := fx) x.store x.conts x.frame W hs X y := by
  induction h with
  | core _ => exact fun W hs X _ hx => absurd hx (core_ne_cvals_cons rfl)
  | @seq _ _ _ _ _ _ vs es _ rest h _ ih =>
    intro W hs X _ hx
    rcases seq_split rfl hx with ⟨V, hV⟩ | ⟨W₂, T₁, rfl, rfl, hT⟩
    · exact (no_step_cvals h V hV).elim
    · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hT.symm
      exact prefixRes_seq h (fun hW => ih W₂ hs X hW rfl)
  | invoke hc => exact fun W hs X _ hx => absurd hx (invoke_ne hc (by simp))
  | _ =>
    intro W hs X hW hx
    first
    | exact (single_ne hW hx).elim
    | fnvX_absurd hx

end Silmaril.Proofs.Wasm.Models.FXLower
