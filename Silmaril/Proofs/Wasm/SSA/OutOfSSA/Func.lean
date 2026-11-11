module

public import Silmaril.Proofs.Wasm.SSA.OutOfSSA.Sim

/-!
# Out of SSA: functions

Every terminating outcome of an SSA function is an outcome of its
decompilation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.OutOfSSA

open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (extend Env)
open Silmaril.Wasm (IntType)

/-- The decompiler's initial context. -/
def initDCtx (f : SFunc) : DCtx where
  vars := (f.params.mapIdx fun j t => VLoc.loc j t).reverse
  labels := [.ret, .trap]
  wdepth := 1
  fty := f.result

theorem decompileFunc_spec {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g) :
    ∃ code s, dR (initDCtx f) f.body ⟨f.params.length, []⟩ = some (code, s) ∧
      s.next = f.params.length + s.types.length ∧
      g = ⟨f.params, s.types.reverse, f.result, code ++ [Expr.unreachable]⟩ := by
  unfold decompileFunc at hd
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hd
  obtain ⟨⟨code, s⟩, h₁, hd⟩ := hd
  by_cases hs : s.next = f.params.length + s.types.length
  · simp only [hs, guard, ite_true, Option.pure_def,
      Option.some.injEq] at hd
    obtain ⟨_, -, rfl⟩ := hd
    exact ⟨code, s, h₁, hs, rfl⟩
  · simp [hs] at hd

theorem decompileFunc_params {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g) :
    g.params = f.params ∧ g.result = f.result := by
  obtain ⟨_, _, _, _, rfl⟩ := decompileFunc_spec hd
  exact ⟨rfl, rfl⟩

theorem varsOK_initial {params : List IntType} {args : List WVal}
    (hl : args.length = params.length) (rest : List WVal) :
    VarsOK (args ++ rest) (params.mapIdx fun j t => VLoc.loc j t).reverse (argEnv args) := by
  intro i V hV
  have hi : i < params.length := by
    by_contra h
    rw [List.getElem?_eq_none (by simp; omega)] at hV
    cases hV
  rw [List.getElem?_reverse (by simpa using hi), List.getElem?_mapIdx] at hV
  simp only [List.length_mapIdx, Option.map_eq_some_iff] at hV
  obtain ⟨t, -, rfl⟩ := hV
  have hj : params.length - 1 - i < args.length := by omega
  obtain ⟨a, ha⟩ : ∃ a, args[params.length - 1 - i]? = some a :=
    ⟨_, List.getElem?_eq_getElem hj⟩
  simp only [readL, List.getElem?_append_left hj, ha, Option.map_some, argEnv]
  rw [List.getElem?_reverse (by omega), hl, ha]

theorem seq_append_abrupt {ls : List WVal} {r : Option WVal} :
    ∀ {A : List Expr} {o : Out (Option WVal)}, Seq ls r A o → o.Abrupt →
      ∀ (B : List Expr), Seq ls r (A ++ B) o
  | [], _, h, hab, _ => by cases h; exact absurd hab id
  | _ :: _, _, h, hab, B => by
      cases h with
      | cons hx hs => exact .cons hx (seq_append_abrupt hs hab B)
      | abrupt hx hab' => exact .abrupt hx hab'

/-- The initial context: parameters are the locals below their count, and no
label is a Wasm block. -/
private theorem initDCtx_wf (f : SFunc) : WF (initDCtx f) f.params.length := by
  refine ⟨fun V hV x hx => ?_, fun w L hL => by simp [initDCtx] at hL⟩
  have hV' : ∃ (j : Nat) (_ : j < f.params.length), VLoc.loc j f.params[j] = V := by
    simpa only [initDCtx, List.mem_reverse, List.mem_mapIdx] using hV
  obtain ⟨j, hj, rfl⟩ := hV'
  have hxj : x = j := by simpa [VLoc.locs] using hx
  omega

/-- An exit of the function body that decodes to `o` is a function exit with
outcome `o`. -/
private theorem initDCtx_exit {f : SFunc} {ls : List WVal} {base l : Nat} {v : SVal}
    {o : FOut} {out : Out (Option WVal)} (hdec : decodeOut l v = some o)
    (hlo : LabelOut (initDCtx f).labels (initDCtx f).wdepth (initDCtx f).fty ls base l v out) :
    out.Abrupt ∧ funcExit f.result out = some o := by
  match l, v, hdec, hlo with
  | 0, .unit, hdec, hlo =>
      have ho : o = .ret none := by simpa [decodeOut, eq_comm] using hdec
      have hout : out = .ret none := by simpa [LabelOut, initDCtx] using hlo
      rw [ho, hout]
      exact ⟨trivial, by simp [funcExit, blockRes]⟩
  | 0, .atom w, hdec, hlo =>
      have ho : o = .ret (some w) := by simpa [decodeOut, eq_comm] using hdec
      obtain ⟨hout, hf⟩ : out = .ret (some w) ∧ f.result.isSome = true := by
        simpa [LabelOut, initDCtx] using hlo
      rw [ho, hout]
      exact ⟨trivial, by simp [funcExit, blockRes, hf]⟩
  | 1, .unit, hdec, hlo =>
      have ho : o = .trap := by simpa [decodeOut, eq_comm] using hdec
      have hout : out = .trap := by simpa [LabelOut, initDCtx] using hlo
      rw [ho, hout]
      exact ⟨trivial, rfl⟩
  | 0, .pair .., hdec, _ | 0, .inl _, hdec, _ | 0, .inr _, hdec, _
  | 1, .atom _, hdec, _ | 1, .pair .., hdec, _ | 1, .inl _, hdec, _ | 1, .inr _, hdec, _ =>
      simp [decodeOut] at hdec
  | l + 2, _, hdec, _ => simp [decodeOut] at hdec

/-- **Out-of-SSA soundness.** -/
theorem decompileFunc_sound {f : SFunc} {g : FragFunc} (hd : decompileFunc f = some g)
    {args : List WVal} {o : FOut} (h : f.Run args o) : g.Run args o := by
  obtain ⟨code, s, hdr, hs, rfl⟩ := decompileFunc_spec hd
  obtain ⟨hty, l, v, hev, hdec⟩ := h
  have hl : args.length = f.params.length := by rw [← hty]; simp
  refine ⟨hty, ?_⟩
  obtain ⟨out, hseq, hlo⟩ := sim hev _ _ _ _ (args ++ s.types.reverse.map WVal.zero) hdr
    (varsOK_initial hl _) (initDCtx_wf f) (by simp [hl, hs])
  obtain ⟨hab, hexit⟩ := initDCtx_exit hdec hlo
  exact ⟨out, seq_append_abrupt hseq hab _, hexit⟩

end Silmaril.Proofs.Wasm.SSA.OutOfSSA
