module

public import Silmaril.Proofs.Wasm.Det.Stateless.Check
public import Silmaril.Proofs.Wasm.Det.Stateless.VC
public import Silmaril.Wasm.Det.Stateless.Litmus.Defs
public import Silmaril.Wasm.Det.Core.Litmus.Thms

/-!
# Litmus module for stateless code (proofs)

* `scratch_stateless`: the function `scratch` (write the argument to the scratch global, read it
  back, add one) meets "returns its argument plus one" in every run from every store holding it
  with the scratch global (the every-run Hoare logic of `Silmaril.Wasm.Logic.Hoare`, with the rules
  `hwp_globalSet`/`hwp_globalGet`), so it is stateless over these stores, at every profile;
* `bump_run`, `read_run`: explicit Core runs (`bump` writes `1` to the counter; `read` returns
  the counter) built rule by rule, at every profile.

The shapes of the allocated functions are computed by kernel evaluation (`decide +kernel`) of
Boolean checks (`shape`), as in `Silmaril.Proofs.Wasm.Det.Core.Litmus`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Stateless.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Det.Stateless Silmaril.Wasm.Det.Stateless.Litmus Silmaril.Wasm.Logic.Hoare
  Silmaril.Proofs.Wasm.Det.Stateless
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Proofs.Wasm.Det.Core.Litmus (steps_invoke_nil expand_of_funcType?)

/-! ## Shapes -/

/-- The body of `scratch`. -/
def scratchB : List Instr → Bool
  | [.localGet x, .globalSet g, .globalGet g', .intConst .i32 c, .intBinOp .i32 .add] =>
    decide (x = ⟨0⟩ ∧ g = ⟨2⟩ ∧ g' = ⟨2⟩ ∧ c = 1)
  | _ => false

/-- The body of `bump`. -/
def bumpB : List Instr → Bool
  | [.globalGet g, .intConst .i32 c, .intBinOp .i32 .add, .globalSet g'] =>
    decide (g = ⟨0⟩ ∧ c = 1 ∧ g' = ⟨0⟩)
  | _ => false

/-- The body of `read`. -/
def readB : List Instr → Bool
  | [.globalGet g] => decide (g = ⟨0⟩)
  | _ => false

/-- The shape of a function of `slMod`: Wasm code without locals passing `body`, of type `ty`, in
a module instance whose global `i` is at address `i`. -/
def shape (body : List Instr → Bool) (ty : List Validation.CValType × List Validation.CValType)
    (fi : FuncInst Nat) : Bool :=
  (match fi.code with
    | .wasm fn => fn.locals.isEmpty && body fn.body
    | .host _ => false) &&
  decide (fi.type.funcType? = some ty) && decide (fi.module.globals = [0, 1, 2])

/-- `[i32] → [i32]`. -/
abbrev tyI : List Validation.CValType × List Validation.CValType :=
  ([.num (.int .i32)], [.num (.int .i32)])

theorem sh_scratch : slStore.funcs[6]?.map (shape scratchB tyI) = some true := by decide +kernel
theorem sh_bump : slStore.funcs[3]?.map (shape bumpB ([], [])) = some true := by decide +kernel
theorem sh_read : slStore.funcs[4]?.map (shape readB ([], [.num (.int .i32)])) = some true := by
  decide +kernel
theorem sl_globals_length : slStore.globals.length = 3 := by decide +kernel
theorem sl_cnt : slStore.globals[0]?.map GlobalInst.value = some (Val.i32 0) := by decide +kernel

theorem shape_spec {i : Nat} {body : List Instr → Bool}
    {ty : List Validation.CValType × List Validation.CValType}
    (h : slStore.funcs[i]?.map (shape body ty) = some true) :
    ∃ fi fn, slStore.funcs[i]? = some fi ∧ fi.code = .wasm fn ∧ fn.locals = [] ∧
      body fn.body = true ∧ fi.type.funcType? = some ty ∧ fi.module.globals = [0, 1, 2] := by
  rcases hfi : slStore.funcs[i]? with _ | fi
  · rw [hfi] at h
    cases h
  · rw [hfi] at h
    have hs : shape body ty fi = true := Option.some.inj h
    rcases hc : fi.code with fn | hh
    · have hs' : (fn.locals.isEmpty = true ∧ body fn.body = true) ∧
          fi.type.funcType? = some ty ∧ fi.module.globals = [0, 1, 2] := by
        simpa only [shape, hc, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hs
      exact ⟨fi, fn, rfl, hc, List.isEmpty_iff.mp hs'.1.1, hs'.1.2, hs'.2.1, hs'.2.2⟩
    · have hb : shape body ty fi = false := by simp [shape, hc]
      rw [hb] at hs
      cases hs

theorem scratchB_eq {b : List Instr} (h : scratchB b = true) : b = scratchBody := by
  unfold scratchB at h
  split at h
  · rename_i x g g' c
    have h' : x = ⟨0⟩ ∧ g = ⟨2⟩ ∧ g' = ⟨2⟩ ∧ c = 1 := of_decide_eq_true h
    rw [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2]
    rfl
  · cases h

theorem bumpB_eq {b : List Instr} (h : bumpB b = true) :
    b = [.globalGet ⟨0⟩, .intConst .i32 1, .intBinOp .i32 .add, .globalSet ⟨0⟩] := by
  unfold bumpB at h
  split at h
  · rename_i g c g'
    have h' : g = ⟨0⟩ ∧ c = 1 ∧ g' = ⟨0⟩ := of_decide_eq_true h
    rw [h'.1, h'.2.1, h'.2.2]
  · cases h

theorem readB_eq {b : List Instr} (h : readB b = true) : b = [.globalGet ⟨0⟩] := by
  unfold readB at h
  split at h
  · rename_i g
    have h' : g = ⟨0⟩ := of_decide_eq_true h
    rw [h']
  · cases h

/-! ## `scratch` by the Hoare logic -/

/-- The result of `scratch`: its argument plus one. -/
def scratchF : List Val → List Val
  | [.num ⟨.int .i32, m⟩] => [.num ⟨.int .i32, m + 1⟩]
  | _ => []

/-- The specification of `scratch` (function instance `fi`): from a store holding it with the
scratch global, on an `i32`, the call returns the argument plus one. -/
def scratchSpec (fi : FuncInst Nat) : FSpec Nat where
  pre s args := s.funcs[6]? = some fi ∧ 2 < s.globals.length ∧ ∃ m : BitVec 32, args = [Val.i32 m]
  post _ args _ o := o = .normal (scratchF args)

theorem global?_scratch {s : Store Nat} {f : Frame} (hm : f.module.globals = [0, 1, 2])
    (hl : 2 < s.globals.length) : s.global? f ⟨2⟩ = some (2, s.globals[2]) := by
  simp [Store.global?, hm, Idx.toNat, List.getElem?_eq_getElem hl]

theorem setGlobal_length (s : Store Nat) (a : Nat) (v : Val) :
    (s.setGlobal a v).globals.length = s.globals.length := List.length_modify ..

theorem add_ok {m : BitVec 32} {z : Numerics.IntValue .i32}
    (h : Numerics.intBinOp .i32 .add m 1 = .ok z) : z = (m + 1 : BitVec 32) := by
  simp only [Numerics.intBinOp, Except.ok.injEq] at h
  exact h.symm

/-- The body of `scratch` returns its argument plus one, in every run from every store with the
scratch global. -/
theorem scratch_body {P : Profile} {s : Store Nat} {fi : FuncInst Nat} {code : Func} {n k : Nat}
    {f : Frame} {vs₀ : List Val} {m : BitVec 32} (hbody : code.body = scratchBody)
    (hm : fi.module.globals = [0, 1, 2]) (hl : 2 < s.globals.length)
    (hrs : k = 1) :
    HWP P Det.noHost s (Frame.forCall fi.module [Val.i32 m] code.locals) (expression code.body)
      (bodyPostK P Det.noHost k f vs₀
        (callPost f vs₀ ((scratchSpec fi).post s [Val.i32 m])) n) := by
  let F := Frame.forCall fi.module [Val.i32 m] code.locals
  let Q := bodyPostK P Det.noHost k f vs₀ (callPost f vs₀ ((scratchSpec fi).post s [Val.i32 m])) n
  let s' := s.setGlobal 2 (Val.i32 m)
  have hFm : F.module.globals = [0, 1, 2] := hm
  have hloc0 : F.local? ⟨0⟩ = some (some (Val.i32 m)) := by
    simp [F, Frame.forCall, Frame.local?, Idx.toNat]
  have hl' : 2 < s'.globals.length := by rw [setGlobal_length]; exact hl
  have hg : s.global? F ⟨2⟩ = some (2, s.globals[2]) := global?_scratch hFm hl
  have hg' : s'.global? F ⟨2⟩ = some (2, s'.globals[2]) := global?_scratch hFm hl'
  have hv : (s'.globals[2]).value = Val.i32 m := by
    simp [s', Store.setGlobal]
  have hq : Q s' F (.normal [Val.i32 (m + 1)]) := ⟨by simp [hrs], rfl, .inl ⟨_, rfl, rfl⟩⟩
  have h₄ : HWP P Det.noHost s' F (vals ([] ++ [Val.num ⟨.int .i32, m⟩, .num ⟨.int .i32, 1⟩]) ++
      .plain (.intBinOp .i32 .add) :: []) Q := by
    refine HWP.intBinOp (fun z hz => ?_) fun e he => by simp [Numerics.intBinOp] at he
    rw [add_ok hz]
    exact HWP.of_vals hq
  have h₃ : HWP P Det.noHost s' F (vals ([] ++ [(s'.globals[2]).value]) ++
      [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .add)]) Q := by
    rw [hv]
    exact h₄
  have h₂ : HWP P Det.noHost s' F (vals [] ++ .plain (.globalGet ⟨2⟩) ::
      [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .add)]) Q := hwp_globalGet hg' h₃
  have h₁ : HWP P Det.noHost s F (vals ([] ++ [Val.i32 m]) ++ .plain (.globalSet ⟨2⟩) ::
      [.plain (.globalGet ⟨2⟩), .plain (.intConst .i32 1), .plain (.intBinOp .i32 .add)]) Q :=
    hwp_globalSet hg h₂
  have h₀ : HWP P Det.noHost s F (vals [] ++ .plain (.localGet ⟨0⟩) ::
      [.plain (.globalSet ⟨2⟩), .plain (.globalGet ⟨2⟩), .plain (.intConst .i32 1),
        .plain (.intBinOp .i32 .add)]) Q := HWP.localGet hloc0 h₁
  rw [hbody]
  exact h₀

/-- Expansions of a function type agree. -/
theorem expand_unique {d : Validation.DefType} {ps rs ps' rs' : Validation.Ty (.list .val)}
    (h : Validation.Expand d (.func ps rs)) (h' : Validation.Expand d (.func ps' rs')) :
    ps' = ps ∧ rs' = rs := by
  have e := (Validation.Expand.iff.mp h).symm.trans (Validation.Expand.iff.mp h')
  injection e with e
  injection e with e₁ e₂
  exact ⟨e₁.symm, e₂.symm⟩

/-- **`scratch` meets its specification**, in every run, at every profile. -/
theorem scratch_valid (P : Profile) :
    ∃ fi, slStore.funcs[6]? = some fi ∧ FSpecValid P Det.noHost 6 (scratchSpec fi) ∧
      ∃ ps rs, Validation.Expand fi.type (.func ps rs) ∧ ps.toList = [.num (.int .i32)] := by
  obtain ⟨fi, fn, hfi, hcode, -, hb, hty, hm⟩ := shape_spec sh_scratch
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  refine ⟨fi, hfi, fun n => ?_, ps, rs, he, hps⟩
  cases n with
  | zero => exact fun _ _ _ _ _ _ _ => trivial
  | succ n =>
    have hlen : ∀ s args, (scratchSpec fi).pre s args → args.length = ps.length := by
      rintro s args ⟨-, -, m, rfl⟩
      show 1 = ps.toList.length
      rw [hps]
      rfl
    have hrs1 : rs.length = 1 := by
      show rs.toList.length = 1
      rw [hrs]
      rfl
    refine FSpecAt.of_body (fun _ _ h => h.1) hcode he hlen fun s args hpre f vs₀ => ?_
    obtain ⟨-, hl, m, rfl⟩ := hpre
    exact scratch_body (scratchB_eq hb) hm hl hrs1 n

theorem valOk_i32 {s : Store Nat} {v : Val} (h : ValOk s v (.num (.int .i32))) :
    ∃ m : BitVec 32, v = Val.i32 m := by
  generalize ht : (.num (.int .i32) : Validation.CValType) = t at h
  cases h with
  | num nv =>
    obtain ⟨ty, b⟩ := nv
    have hty : ty = .int .i32 := by injection ht with h; exact h.symm
    subst hty
    exact ⟨b, rfl⟩
  | vec b => cases ht
  | ref _ => cases ht

/-- **`scratch` is stateless** over the stores holding it with the scratch global, at every
profile: by its every-run specification. -/
theorem scratch_stateless (P : Profile) :
    StatelessFn P (fun s => s.funcs = slStore.funcs ∧ 2 < s.globals.length) 6 := by
  obtain ⟨fi, hfi, hv, ps, rs, he, hps⟩ := scratch_valid P
  refine statelessFn_of_fspec scratchF hv (fun s vs hs hok => ?_) fun _ _ _ _ h => .inl h
  obtain ⟨fi', ps', rs', hfi', he', hvs⟩ := hok
  have hfi'' : s.funcs[6]? = some fi := by rw [hs.1]; exact hfi
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi'')
  obtain ⟨rfl, -⟩ := expand_unique he he'
  rw [hps] at hvs
  obtain ⟨v, hv', rfl⟩ : ∃ v, ValOk s v (.num (.int .i32)) ∧ vs = [v] := by
    cases hvs with
    | cons h₁ h₂ => cases h₂; exact ⟨_, h₁, rfl⟩
  obtain ⟨m, rfl⟩ := valOk_i32 hv'
  exact ⟨hfi'', hs.2, m, rfl⟩

/-! ## The counter: explicit runs -/

theorem invokeOk_nil' {i : Nat} {body : List Instr → Bool} {rs' : List Validation.CValType}
    (h : slStore.funcs[i]?.map (shape body ([], rs')) = some true) {s : Store Nat}
    (hs : s.funcs = slStore.funcs) : InvokeOk s i [] := by
  obtain ⟨fi, -, hfi, -, -, -, hty, -⟩ := shape_spec h
  obtain ⟨ps, rs, he, hps, -⟩ := expand_of_funcType? hty
  refine ⟨fi, ps, rs, by rw [hs]; exact hfi, he, ?_⟩
  rw [hps]
  exact .nil

/-- The counter after `bump`. -/
def slStore₁ : Store Nat := slStore.setGlobal 0 (Val.i32 1)

/-- The value of the counter. -/
theorem cnt_value {s : Store Nat} {f : Frame} (hm : f.module.globals = [0, 1, 2]) {v : Val}
    (hv : s.globals[0]?.map GlobalInst.value = some v) :
    ∃ g, s.global? f ⟨0⟩ = some (0, g) ∧ g.value = v := by
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨g, by simp [Store.global?, hm, Idx.toNat, hg], rfl⟩

theorem cnt_value₁ : slStore₁.globals[0]?.map GlobalInst.value = some (Val.i32 1) := by
  have hl : 0 < slStore.globals.length := by rw [sl_globals_length]; decide
  simp [slStore₁, Store.setGlobal, List.getElem?_eq_getElem hl]

/-- **`bump` writes `1` to the counter**, at every profile. -/
theorem bump_run (P : Profile) :
    Steps P Det.noHost (invoke slStore 3 []) ⟨slStore₁, {}, vals []⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hloc, hb, hty, hm⟩ := shape_spec sh_bump
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  let F := Frame.forCall fi.module [] fn.locals
  obtain ⟨g, hg, hgv⟩ := cnt_value (f := F) hm sl_cnt
  have hs₁ : Step P Det.noHost ⟨slStore, F, vals [] ++ [.plain (.globalGet ⟨0⟩)] ++
      [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .add), .plain (.globalSet ⟨0⟩)]⟩
      ⟨slStore, F, vals [] ++ [g.value.toAdmin] ++
        [.plain (.intConst .i32 1), .plain (.intBinOp .i32 .add), .plain (.globalSet ⟨0⟩)]⟩ :=
    .ctxtInstrs (.variable (.globalGet hg)) (.inr (by simp))
  have hs₂ : Step P Det.noHost ⟨slStore, F, vals [] ++ [.plain (.intConst .i32 0),
      .plain (.intConst .i32 1), .plain (.intBinOp .i32 .add)] ++ [.plain (.globalSet ⟨0⟩)]⟩
      ⟨slStore, F, vals [] ++ [.plain (.intConst .i32 1)] ++ [.plain (.globalSet ⟨0⟩)]⟩ :=
    .ctxtInstrs (.numeric (.intBinOp rfl)) (.inr (by simp))
  have hs₃ : Step P Det.noHost ⟨slStore, F, [(Val.i32 1).toAdmin, .plain (.globalSet ⟨0⟩)]⟩
      ⟨slStore₁, F, []⟩ := .variable (.globalSet hg)
  have hbody : Steps P Det.noHost ⟨slStore, F, expression fn.body⟩ ⟨slStore₁, F, vals []⟩ := by
    rw [bumpB_eq hb]
    have h₁ : g.value.toAdmin = .plain (.intConst .i32 0) := by rw [hgv]; rfl
    rw [h₁] at hs₁
    exact ((Relation.ReflTransGen.single hs₁).tail hs₂).tail hs₃
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : ([] : List Val).length = rs.length := by
    show 0 = rs.toList.length
    rw [hrs]
    rfl
  exact steps_invoke_nil hfi he hps0 hcode hbody hout

/-- **`read` returns the counter**, at every profile: `0` in `slStore`, `1` after `bump`. -/
theorem read_run (P : Profile) {s : Store Nat} {v : Val} (hs : s.funcs = slStore.funcs)
    (hv : s.globals[0]?.map GlobalInst.value = some v) :
    Steps P Det.noHost (invoke s 4 []) ⟨s, {}, vals [v]⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hloc, hb, hty, hm⟩ := shape_spec sh_read
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hfi' : s.funcs[4]? = some fi := by rw [hs]; exact hfi
  let F := Frame.forCall fi.module [] fn.locals
  obtain ⟨g, hg, hgv⟩ := cnt_value (f := F) hm hv
  have hbody : Steps P Det.noHost ⟨s, F, expression fn.body⟩ ⟨s, F, vals [v]⟩ := by
    rw [readB_eq hb]
    have h₁ := Relation.ReflTransGen.single (r := Step P Det.noHost) (.variable (.globalGet hg))
    rw [hgv] at h₁
    exact h₁
  have hps0 : ps.length = 0 := by
    show ps.toList.length = 0
    rw [hps]
    rfl
  have hout : [v].length = rs.length := by
    show 1 = rs.toList.length
    rw [hrs]
    rfl
  exact steps_invoke_nil hfi' he hps0 hcode hbody hout

end Silmaril.Proofs.Wasm.Det.Stateless.Litmus
