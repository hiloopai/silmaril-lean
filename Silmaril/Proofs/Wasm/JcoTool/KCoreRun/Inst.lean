module

public import Silmaril.Wasm.JcoTool.KCoreRun.Defs
public import Silmaril.Wasm.Execution.Core.Exec.ConstEvalComplete

/-!
# Core instantiation of the emitted module

`toModule_inst`: Core 3.0 instantiation (`Execution.Core.Instantiate`, under any host and profile) of
`KCoreEmit.toModule P name`, with the eight imported built-ins supplied as host functions (`ImpsOK`),
gives the configuration with no code left to run (no segments, no start function), whose module
instance holds the lift at function `9` (`EntryAt`), the callback at function `10` (`CbAt`), and
whose store holds the nine globals at `P.g0` and the memory of `MSZ` zero bytes (`InstR`).

The pieces: a configuration of values does not step under any host (`no_step_vals`, by silmaril's
`Step.const_redex`); so a constant initializer evaluates to its value in place (`evalExpr_c32`,
`evalGlobals_c32`); `allocModule?` on `toModule` (`alloc_toModule`): the three functions after the
imports, the memory and the nine globals at the ends of the store's lists.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreEmit
open Silmaril.Wasm.JcoTool.KCore (Prog BI M32)
open Silmaril.Wasm.JcoTool.KCoreRun

variable {H : Type}

/-! ## Constant initializers -/

theorem no_step_vals {Pf : Profile} {host : HostSemantics H} {s : Store H} {f : Frame} {W : List Val}
    {c : Config H} (h : Step Pf host ⟨s, f, vals W⟩ c) : False := by
  have hc : ∀ a ∈ (⟨s, f, vals W⟩ : Config H).code, a.ConstOk := fun a ha => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp ha
    exact Admin.constOk_toAdmin v
  obtain ⟨-, pre, w', i, post, out, hcode, -, hr⟩ := Step.const_redex h hc
  have hi : Admin.plain i ∈ vals W := by
    rw [show vals W = _ from hcode]; simp
  obtain ⟨v, -, hv⟩ := List.mem_map.mp hi
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp only [Val.toAdmin, Admin.plain.injEq, reduceCtorEq] at hv <;>
    subst hv <;> cases hr

theorem evalExpr_c32 {Pf : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame} {n : Nat}
    {vs : List Val} (h : EvalExpr Pf host s f [c32 n] s' f' vs) :
    s' = s ∧ f' = f ∧ vs = [Val.i32 (w n)] := by
  have e : expression [c32 n] = vals [Val.i32 (w n)] := rfl
  rcases Relation.ReflTransGen.cases_head (show Steps Pf host _ _ from h) with heq | ⟨c, hs, -⟩
  · have heq' : (⟨s, f, vals [Val.i32 (w n)]⟩ : Config H) = ⟨s', f', vals vs⟩ := by rw [← e]; exact heq
    obtain ⟨rfl, rfl, hv⟩ := Config.mk.inj heq'
    exact ⟨rfl, rfl, (vals_inj hv).symm⟩
  · exact (no_step_vals (show Step Pf host ⟨s, f, vals [Val.i32 (w n)]⟩ c by rw [← e]; exact hs)).elim

theorem evalGlobals_c32 {Pf : Profile} {host : HostSemantics H} {s s' : Store H} {f f' : Frame}
    {gts : List CGlobalType} {es : List Expr} {vs : List Val}
    (h : EvalGlobals Pf host s f gts es s' f' vs) :
    ∀ ns : List Nat, es = ns.map (fun n => [c32 n]) →
      vs = ns.map (fun n => Val.i32 (w n)) ∧ s'.funcs = s.funcs ∧ s'.mems = s.mems := by
  induction h with
  | nil => intro ns hns; cases ns with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons _ _ => cases hns
  | cons he _ ih =>
    intro ns hns
    match ns, hns with
    | n :: ns', hns =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hns
      obtain ⟨rfl, rfl, hv⟩ := evalExpr_c32 he
      obtain ⟨hvs, hf, hm⟩ := ih ns' rfl
      exact ⟨by rw [List.map_cons, hvs, ← List.singleton_inj.mp hv], hf, hm⟩

/-! ## Allocation -/

theorem allocMany_global (s : Store H) : ∀ ps : List (CGlobalType × Val),
    allocMany (fun s p => allocGlobal s p.1 p.2) s ps =
      ({ s with globals := s.globals ++ ps.map (fun p => ⟨p.1, p.2⟩) },
        (List.range ps.length).map (s.globals.length + ·))
  | [] => by simp [allocMany]
  | p :: ps => by
    have e := allocMany_global (allocGlobal s p.1 p.2).1 ps
    simp only [allocMany, e]
    simp only [allocGlobal, List.length_append, List.append_assoc,
      List.singleton_append, List.map_cons, List.length_cons, List.length_nil, List.range_succ_eq_map, List.map_map,
      Prod.mk.injEq, List.cons.injEq, Nat.add_zero, true_and]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp]
    omega

theorem allocMany_func (s : Store H) (mi : ModuleInst) : ∀ ps : List (DefType × Func),
    allocMany (fun s p => allocFunc s p.1 (.wasm p.2) mi) s ps =
      ({ s with funcs := s.funcs ++ ps.map (fun p => ⟨p.1, mi, .wasm p.2⟩) },
        (List.range ps.length).map (s.funcs.length + ·))
  | [] => by simp [allocMany]
  | p :: ps => by
    have e := allocMany_func (allocFunc s p.1 (.wasm p.2) mi).1 mi ps
    simp only [allocMany, e]
    simp only [allocFunc, List.length_append, List.append_assoc,
      List.singleton_append, List.map_cons, List.length_cons, List.length_nil, List.range_succ_eq_map, List.map_map,
      Prod.mk.injEq, List.cons.injEq, Nat.add_zero, true_and]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp]
    omega

theorem xa_funcs : ∀ as : List Nat, ExternAddr.funcs (as.map .func) = as
  | [] => rfl
  | a :: as => by simp [ExternAddr.funcs, xa_funcs as]
theorem xa_globals : ∀ as : List Nat, ExternAddr.globals (as.map .func) = []
  | [] => rfl
  | a :: as => by simp [ExternAddr.globals, xa_globals as]
theorem xa_mems : ∀ as : List Nat, ExternAddr.mems (as.map .func) = []
  | [] => rfl
  | a :: as => by simp [ExternAddr.mems, xa_mems as]
theorem xa_tags : ∀ as : List Nat, ExternAddr.tags (as.map .func) = []
  | [] => rfl
  | a :: as => by simp [ExternAddr.tags, xa_tags as]
theorem xa_tables : ∀ as : List Nat, ExternAddr.tables (as.map .func) = []
  | [] => rfl
  | a :: as => by simp [ExternAddr.tables, xa_tables as]

/-- The closed type `i` of the module. -/
def D (i : Nat) : DefType := (allocTypes types).getD i default

theorem dts_get (i : Nat) (hi : i < 7) : (allocTypes types)[i]? = some (D i) := by
  have hl : (allocTypes types).length = 7 := by decide
  rw [D, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

def cbF (P : Prog) : Func := ⟨ix 2, [i32, i32, i32, i32, i64], sCode P.cb ++ [.unreachable]⟩
def enF (P : Prog) : Func := ⟨ix 6, [i32, i32, i32, i32, i32, i32, i64], sCode P.entry ++ [.unreachable]⟩
def reF : Func := ⟨ix 5, [], [c32 0x8000]⟩
def gT : CGlobalType := ⟨.var, Ty.substAll (liftVal i32) ((allocTypes types).map Ty.dt)⟩

theorem ix_type_toNat (n : Nat) (hn : n < 2 ^ 32) : Idx.toNat (ix (k := .type_) n) = n :=
  Nat.mod_eq_of_lt hn

theorem alloc_toModule {P : Prog} {name : String} {s : Store H} {as : List Nat} {vs : List Val}
    {s₄ : Store H} {mi : ModuleInst} (hlen : vs.length = 9)
    (h : allocModule? s (toModule P name) (as.map .func) vs [] [] = some (s₄, mi)) :
    mi.funcs = as ++ [s.funcs.length, s.funcs.length + 1, s.funcs.length + 2] ∧
      mi.mems = [s.mems.length] ∧ mi.globals = (List.range 9).map (s.globals.length + ·) ∧
      s₄.funcs = s.funcs ++ [⟨D 5, mi, .wasm reF⟩, ⟨D 6, mi, .wasm (enF P)⟩, ⟨D 2, mi, .wasm (cbF P)⟩] ∧
      s₄.mems = s.mems ++ [⟨⟨.i32, ⟨2, none⟩⟩, ⟨Array.replicate (2 * Execution.Memory.pageSize) 0⟩⟩] ∧
      s₄.globals = s.globals ++ vs.map (⟨gT, ·⟩) := by
  simp only [allocModule?, toModule, allocMany, List.map_nil, List.zip_nil_right,
    pure, allocMany_global, allocMany_func, Option.bind_eq_bind,
    xa_funcs, xa_globals, xa_mems, xa_tags, xa_tables, List.nil_append, List.append_nil,
    allocMem, Option.bind_eq_some_iff, List.mapM_nil, List.mapM_cons, Func.type,
    ix_type_toNat 5 (by decide), ix_type_toNat 6 (by decide), ix_type_toNat 2 (by decide),
    dts_get 5 (by decide), dts_get 6 (by decide), dts_get 2 (by decide), Option.bind_some,
    Option.some.injEq] at h
  obtain ⟨xi, -, h⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  simp only [List.length_zip, hlen, Nat.min_self, List.length_cons,
    List.length_nil, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.nil_append, List.cons_append, List.zip_nil_right, true_and]
  match vs, hlen with
  | [_, _, _, _, _, _, _, _, _], _ => repeat' constructor

/-! ## Instantiation -/

theorem bv_mod (n : Nat) : w (n % M32) = w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [w, BitVec.toNat_ofNat, M32, Nat.mod_mod]

theorem expand_D2 : ∃ ps rs, Expand (D 2) (.func ps rs) ∧ ps.length = 3 ∧ rs.length = 1 :=
  ⟨_, _, Expand.iff.mpr rfl, rfl, rfl⟩

theorem expand_D6 : ∃ ps rs, Expand (D 6) (.func ps rs) ∧ ps.length = 1 ∧ rs.length = 1 :=
  ⟨_, _, Expand.iff.mpr rfl, rfl, rfl⟩

/-- What instantiation leaves: the globals' values, the allocation, no code. -/
theorem inst_run {Pf : Profile} {host : HostSemantics H} {s : Store H} {P : Prog} {name : String}
    {as : List Nat} {c : Config H} (hI : Instantiate Pf host s (toModule P name) (as.map .func) c) :
    ∃ (s₃ s₄ : Store H) (mi : ModuleInst) (vs : List Val),
      vs = ((List.range 9).map P.g0).map (fun n => Val.i32 (w n)) ∧ s₃.funcs = s.funcs ∧
      allocModule? s₃ (toModule P name) (as.map .func) vs [] [] = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi }, []⟩ := by
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vs, rT, rE, mi, hG, hT, hE, hA, rfl⟩ := hI.run
  cases hT
  cases hE
  have hes : (toModule P name).globals.map Global.init = ((List.range 9).map P.g0).map (fun n => [c32 n]) := by
    simp only [toModule, List.map_map]; rfl
  obtain ⟨hvs, hf, -⟩ := evalGlobals_c32 hG _ hes
  exact ⟨s₁, s₄, mi, vs, hvs, hf, hA, rfl⟩

/-- The globals `GlobalsAre` asks for. -/
theorem inst_globals {s₃ s₄ : Store H} {mi : ModuleInst} {P : Prog}
    (hg : mi.globals = (List.range 9).map (s₃.globals.length + ·))
    (hs : s₄.globals = s₃.globals ++ (((List.range 9).map P.g0).map (fun n => Val.i32 (w n))).map (⟨gT, ·⟩)) :
    Silmaril.Wasm.FX.Asyncify.Tool.GlobalsAre s₄ ⟨[], mi⟩ (gsOf fun i => P.g0 i % M32) := by
  have hat : ∀ i, i < 9 → s₄.global? ⟨[], mi⟩ (Silmaril.Wasm.FX.Asyncify.Tool.gidx i) =
      some (s₃.globals.length + i, ⟨gT, Val.i32 (w (P.g0 i))⟩) := fun i hi => by
    have hix : (Silmaril.Wasm.FX.Asyncify.Tool.gidx i).toNat = i := Nat.mod_eq_of_lt (by omega)
    simp only [Store.global?, hix, hg, hs, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, List.map_map]
    rfl
  refine ⟨by simp [gsOf, NG], fun i hi => ?_, fun i j a a' gi gi' hai haj hi hj ha => ?_⟩
  · have hi' : i < 9 := by simpa [gsOf, NG] using hi
    refine ⟨_, _, hat i hi', ?_, rfl⟩
    simp only [gsOf, List.getElem_map, List.getElem_range, bv_mod]
  · have hi' : i < 9 := by simpa [gsOf, NG] using hi
    have hj' : j < 9 := by simpa [gsOf, NG] using hj
    have e₁ : s₃.globals.length + i = a := (Prod.mk.inj (Option.some.inj ((hat i hi').symm.trans hai))).1
    have e₂ : s₃.globals.length + j = a' := (Prod.mk.inj (Option.some.inj ((hat j hj').symm.trans haj))).1
    omega

/-- Memory `0` of the instance: `MSZ` zero bytes. -/
theorem inst_mem {s₃ s₄ : Store H} {mi : ModuleInst} (hm : mi.mems = [s₃.mems.length])
    (hs : s₄.mems = s₃.mems ++ [⟨⟨.i32, ⟨2, none⟩⟩, ⟨Array.replicate (2 * Execution.Memory.pageSize) 0⟩⟩]) :
    ∃ x, mi.mems[0]? = some s₃.mems.length ∧ s₄.mems[s₃.mems.length]? = some x ∧ x.bytes.size = MSZ ∧
      ∀ a (h : a < x.bytes.size), (x.bytes[a]'h).toNat = (fun _ => 0) a := by
  refine ⟨_, by rw [hm]; rfl, by rw [hs, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl,
    ?_, fun a h => ?_⟩
  · show (Array.replicate (2 * 65536) (0 : UInt8)).size = MSZ
    simp only [Array.size_replicate, MSZ]
  · simp [ByteArray.getElem_eq_getElem_data]

/-- The imported built-ins of the instance are the host functions of `ImpsOK`. -/
theorem inst_imp {hb : BI → H} {s s₃ s₄ : Store H} {mi : ModuleInst} {as : List Nat}
    (himp : ImpsOK hb s as) (hf : s₃.funcs = s.funcs) {fs : List Nat} (hmf : mi.funcs = as ++ fs)
    {gs : List (FuncInst H)} (hsf : s₄.funcs = s₃.funcs ++ gs) (b : BI) :
    ∃ a fi ps rs, mi.funcs[biFn b]? = some a ∧ s₄.funcs[a]? = some fi ∧ fi.code = .host (hb b) ∧
      Expand fi.type (.func ps rs) ∧ (b ≠ .taskReturn → ps.length = arity b) := by
  obtain ⟨a, fi, ps, rs, ha, hfi, hc, he, hl⟩ := himp.2 b
  have hb8 : biFn b < as.length := by rw [himp.1]; cases b <;> decide
  have ha' : a < s₃.funcs.length := by rw [hf]; exact (List.getElem?_eq_some_iff.mp hfi).1
  refine ⟨a, fi, ps, rs, ?_, ?_, hc, he, fun _ => hl⟩
  · rw [hmf, List.getElem?_append_left hb8]; exact ha
  · rw [hsf, List.getElem?_append_left ha', hf]; exact hfi

/-- **Core instantiation of the emitted module** (`KCoreEmit.toModule P name`), with the built-ins
supplied as host functions: no code is left to run, the instance holds the lift at function `9`
and the callback at function `10`, and its globals hold `P.g0` (as `i32`s), its memory `MSZ`
zero bytes, its imports the built-ins (`InstR`). -/
theorem toModule_inst {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {P : Prog} {name : String} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s (toModule P name) (as.map .func) c) (himp : ImpsOK hb s as) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun i => P.g0 i % M32) (fun _ => 0) ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module P a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module P a₁₀ := by
  obtain ⟨s₃, s₄, mi, vs, rfl, hf, hA, rfl⟩ := inst_run hI
  obtain ⟨hmf, hmm, hmg, hsf, hsm, hsg⟩ := alloc_toModule (by simp) hA
  have h8 : as.length = 8 := himp.1
  have hfn : ∀ i, i < 3 → mi.funcs[8 + i]? = some (s₃.funcs.length + i) := fun i hi => by
    rw [hmf, List.getElem?_append_right (by omega), h8, Nat.add_sub_cancel_left]
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  have hsn : ∀ i, s₄.funcs[s₃.funcs.length + i]? =
      [(⟨D 5, mi, .wasm reF⟩ : FuncInst H), ⟨D 6, mi, .wasm (enF P)⟩, ⟨D 2, mi, .wasm (cbF P)⟩][i]? :=
    fun i => by rw [hsf, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  obtain ⟨p₉, r₉, he₉, hp₉, hr₉⟩ := expand_D6
  obtain ⟨p₁₀, r₁₀, he₁₀, hp₁₀, hr₁₀⟩ := expand_D2
  refine ⟨rfl, s₃.mems.length, s₃.funcs.length + 1, s₃.funcs.length + 2,
    ⟨inst_globals hmg hsg, fun i _ => Nat.mod_lt _ (by decide), inst_mem hmm hsm,
      inst_imp himp hf hmf hsf⟩, hfn 1 (by decide), ?_, hfn 2 (by decide), ?_⟩
  · exact ⟨_, _, p₉, r₉, hsn 1, rfl, rfl, he₉, hp₉, hr₉⟩
  · exact ⟨_, _, p₁₀, r₁₀, hsn 2, rfl, rfl, he₁₀, hp₁₀, hr₁₀⟩

/-! ## Any arity of `task.return` -/

theorem arityN_ne {n : Nat} {b : BI} (h : b ≠ .taskReturn) : arityN n b = arity b := by
  cases b <;> first | rfl | exact absurd rfl h

theorem impsOK_N {hb : BI → H} {s : Store H} {as : List Nat} (h : ImpsOK hb s as) : ImpsOKN 1 hb s as := by
  refine ⟨h.1, fun b => ?_⟩
  obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := h.2 b
  exact ⟨a, fi, ps, rs, h1, h2, h3, h4, by rw [h5]; cases b <;> rfl⟩

/-- The imported built-ins of the instance, from `ImpsOKN n`. -/
theorem inst_impN {n : Nat} {hb : BI → H} {s s₃ s₄ : Store H} {mi : ModuleInst} {as : List Nat}
    (himp : ImpsOKN n hb s as) (hf : s₃.funcs = s.funcs) {fs : List Nat} (hmf : mi.funcs = as ++ fs)
    {gs : List (FuncInst H)} (hsf : s₄.funcs = s₃.funcs ++ gs) (b : BI) :
    ∃ a fi ps rs, mi.funcs[biFn b]? = some a ∧ s₄.funcs[a]? = some fi ∧ fi.code = .host (hb b) ∧
      Expand fi.type (.func ps rs) ∧ ps.length = arityN n b := by
  obtain ⟨a, fi, ps, rs, ha, hfi, hc, he, hl⟩ := himp.2 b
  have hb8 : biFn b < as.length := by rw [himp.1]; cases b <;> decide
  have ha' : a < s₃.funcs.length := by rw [hf]; exact (List.getElem?_eq_some_iff.mp hfi).1
  refine ⟨a, fi, ps, rs, ?_, ?_, hc, he, hl⟩
  · rw [hmf, List.getElem?_append_left hb8]; exact ha
  · rw [hsf, List.getElem?_append_left ha', hf]; exact hfi

/-- `inst_run` for the emitted module with other imports (instantiation does not read the
imports' declarations past validation). -/
theorem inst_runI {Pf : Profile} {host : HostSemantics H} {s : Store H} {P : Prog} {name : String}
    {is : List Import} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s { toModule P name with imports := is } (as.map .func) c) :
    ∃ (s₃ s₄ : Store H) (mi : ModuleInst) (vs : List Val),
      vs = ((List.range 9).map P.g0).map (fun n => Val.i32 (w n)) ∧ s₃.funcs = s.funcs ∧
      allocModule? s₃ (toModule P name) (as.map .func) vs [] [] = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi }, []⟩ := by
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, vs, rT, rE, mi, hG, hT, hE, hA, rfl⟩ := hI.run
  cases hT
  cases hE
  have hes : ({ toModule P name with imports := is } : Module).globals.map Global.init =
      ((List.range 9).map P.g0).map (fun n => [c32 n]) := by
    simp only [toModule, List.map_map]; rfl
  obtain ⟨hvs, hf, -⟩ := evalGlobals_c32 hG _ hes
  exact ⟨s₁, s₄, mi, vs, hvs, hf, hA, rfl⟩

/-- **Core instantiation of the emitted module with any imports** (`toModule_inst` for
`{ toModule P name with imports := is }`, the built-ins supplied as host functions with
`task.return` of `n` values, `ImpsOKN n`): besides `toModule_inst`'s conclusions, the instance's
`task.return` takes `n` values (`RetAt`). -/
theorem toModuleI_inst {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {P : Prog} {name : String} {is : List Import} {n : Nat} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s { toModule P name with imports := is } (as.map .func) c)
    (himp : ImpsOKN n hb s as) :
    c.code = [] ∧ ∃ ma a₉ a₁₀, InstR hb ma c.store c.frame.module (fun i => P.g0 i % M32) (fun _ => 0) ∧
      RetAt hb c.store c.frame.module n ∧
      c.frame.module.funcs[9]? = some a₉ ∧ EntryAt c.store c.frame.module P a₉ ∧
      c.frame.module.funcs[10]? = some a₁₀ ∧ CbAt c.store c.frame.module P a₁₀ := by
  obtain ⟨s₃, s₄, mi, vs, rfl, hf, hA, rfl⟩ := inst_runI hI
  obtain ⟨hmf, hmm, hmg, hsf, hsm, hsg⟩ := alloc_toModule (by simp) hA
  have h8 : as.length = 8 := himp.1
  have hfn : ∀ i, i < 3 → mi.funcs[8 + i]? = some (s₃.funcs.length + i) := fun i hi => by
    rw [hmf, List.getElem?_append_right (by omega), h8, Nat.add_sub_cancel_left]
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  have hsn : ∀ i, s₄.funcs[s₃.funcs.length + i]? =
      [(⟨D 5, mi, .wasm reF⟩ : FuncInst H), ⟨D 6, mi, .wasm (enF P)⟩, ⟨D 2, mi, .wasm (cbF P)⟩][i]? :=
    fun i => by rw [hsf, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  obtain ⟨p₉, r₉, he₉, hp₉, hr₉⟩ := expand_D6
  obtain ⟨p₁₀, r₁₀, he₁₀, hp₁₀, hr₁₀⟩ := expand_D2
  have himpI := inst_impN himp hf hmf hsf
  refine ⟨rfl, s₃.mems.length, s₃.funcs.length + 1, s₃.funcs.length + 2,
    ⟨inst_globals hmg hsg, fun i _ => Nat.mod_lt _ (by decide), inst_mem hmm hsm, fun b => ?_⟩,
    himpI .taskReturn, hfn 1 (by decide), ?_, hfn 2 (by decide), ?_⟩
  · obtain ⟨a, fi, ps, rs, h1, h2, h3, h4, h5⟩ := himpI b
    exact ⟨a, fi, ps, rs, h1, h2, h3, h4, fun hb' => h5.trans (arityN_ne hb')⟩
  · exact ⟨_, _, p₉, r₉, hsn 1, rfl, rfl, he₉, hp₉, hr₉⟩
  · exact ⟨_, _, p₁₀, r₁₀, hsn 2, rfl, rfl, he₁₀, hp₁₀, hr₁₀⟩

/-- **The `task.return` of the emitted module takes one value** (`ImpsOK`). -/
theorem toModule_ret {Pf : Profile} {host : HostSemantics H} {hb : BI → H} {s : Store H}
    {P : Prog} {name : String} {as : List Nat} {c : Config H}
    (hI : Instantiate Pf host s (toModule P name) (as.map .func) c) (himp : ImpsOK hb s as) :
    RetAt hb c.store c.frame.module 1 :=
  (toModuleI_inst (is := (toModule P name).imports) hI (impsOK_N himp)).2.choose_spec.choose_spec.choose_spec.2.1

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Inst
