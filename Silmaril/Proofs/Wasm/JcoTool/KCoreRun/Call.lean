module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Bi

/-!
# Built-in calls on Core 3.0: the host call of an imported function

`args_run`: the arguments of a call run, left to right, to their values on the stack.
`host_run`: under `Rel`, `call (biFn b)` on those values is Core's `call` step to the imported
function, then the host call of `hb b`, answered by `bans ma b` (the `host` rule of `HStep`),
to the results on the stack, in a store that keeps `Rel` with the memory and host state `bi`
leaves. `call_run`: a statement `call b args dst` that `bexec` runs, as
`KCoreEmit.callCode`, ends normally with the results in the locals `dst`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E BI Out M32 upd)
open Silmaril.Wasm.JcoTool.KDrop (DSt)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode callCode biFn)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma nl : Nat}

theorem stackA_append (xs ops : List W) : stackA (xs ++ ops) = stackA ops ++ stackA xs := by
  simp [stackA, vals]

theorem mapM_cons {s : DSt} {e : E} {es : List E} {as : List Nat}
    (h : (e :: es).mapM (cev nl s) = some as) :
    ∃ a as', cev nl s e = some a ∧ es.mapM (cev nl s) = some as' ∧ as = a :: as' := by
  simp only [List.mapM_cons] at h
  cases ha : cev nl s e with
  | none => rw [ha] at h; cases h
  | some a =>
    cases hs : es.mapM (cev nl s) with
    | none => rw [ha, hs] at h; cases h
    | some as' =>
      rw [ha, hs] at h
      exact ⟨a, as', rfl, rfl, (Option.some.inj h).symm⟩

/-- **The arguments of a call** run to their values, left to right. -/
theorem args_run {q : HQ} {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) :
    ∀ (args : List E) {as : List Nat}, args.mapM (cev nl s) = some as →
      (∀ a ∈ as, a < M32) ∧ ∀ (ops : List W) (rest : List Admin),
        HSteps Pf hb ma (q, ⟨cs, F, stackA ops ++ ((args.map eCode).flatten.map Admin.plain ++ rest)⟩)
          (q, ⟨cs, F, stackA ((as.map w).reverse ++ ops) ++ rest⟩)
  | [], as, hm => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hm
    subst hm
    exact ⟨by simp, fun ops rest => by simpa using Relation.ReflTransGen.refl⟩
  | e :: es, as, hm => by
    obtain ⟨a, as', ha, hs, rfl⟩ := mapM_cons hm
    obtain ⟨hal, ra⟩ := expr_run (Pf := Pf) (q := q) h e ha
    obtain ⟨hsl, rs⟩ := args_run h es hs
    refine ⟨fun x hx => ?_, fun ops rest => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hal
      · exact hsl x hx
    · have e₁ : ((e :: es).map eCode).flatten.map Admin.plain ++ rest =
          (eCode e).map Admin.plain ++ ((es.map eCode).flatten.map Admin.plain ++ rest) := by simp
      have e₂ : ((a :: as').map w).reverse ++ ops = (as'.map w).reverse ++ (w a :: ops) := by simp
      rw [e₁, e₂]
      exact (ra ops _).trans (rs (w a :: ops) rest)

theorem map_toNat {as : List Nat} (h : ∀ a ∈ as, a < M32) : (as.map w).map BitVec.toNat = as := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id as]
  apply List.map_congr_left
  intro a ha
  exact w_toNat (h a ha)

/-- **The host call of a built-in**: Core's `call` of the import, then the host's answer. -/
theorem host_run {cs : Store H} {F : Frame} {s : DSt} (h : Rel hb nl ma cs F s) {b : BI}
    {as : List Nat} (has : ∀ a ∈ as, a < M32) {q' : HQ} {m' : Nat → Nat} {res : List Nat}
    (hbi : bi b as (s.st, s.rp) s.m = some (q', m', res)) (hok : memOK MSZ b as = true)
    (rest : List Admin) :
    ∃ cs', MemR cs' F ma m' ∧ cs'.globals = cs.globals ∧ cs'.funcs = cs.funcs ∧
      HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA (as.map w).reverse ++
          .plain (.call (ix (biFn b))) :: rest⟩)
        (q', ⟨cs', F, stackA (res.map w).reverse ++ rest⟩) := by
  obtain ⟨mi, h0, h1, hs, hbytes⟩ := h.mem
  obtain ⟨a, fi, ps, rs, hfa, hfi, hcode, hexp, har⟩ := h.imp b
  have hag := memOf_agree hs hbytes
  obtain ⟨m₂, hbi₂, hag₂⟩ := bi_congr (fun x hx => (hag x hx).symm) hok hbi
  have hlen := (bi_shape hbi).1
  have hans : bans ma b (s.st, s.rp) cs (as.map w) =
      some (q', cs.setMem ma { mi with bytes := encMem mi.bytes.size m₂ }, res.map w) := by
    have hok' : memOK mi.bytes.size b as = true := hs ▸ hok
    simp only [bans, h1, bind, Option.bind, map_toNat has, hok', ↓reduceIte, hbi₂]
    rfl
  have hm' := memR_enc h.memR (bi_bytes (fun x hx => h.memR.byte_lt hx) hbi) hag₂ h1
  refine ⟨_, hm', rfl, rfl, ?_⟩
  have hx : F.module.funcs[(ix (biFn b) : FuncIdx).toNat]? = some a := by
    have : biFn b < M32 := by cases b <;> decide
    rw [ix_toNat this]; exact hfa
  have r₁ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA (as.map w).reverse ++
        .plain (.call (ix (biFn b))) :: rest⟩)
      ((s.st, s.rp), ⟨cs, F, stackA (as.map w).reverse ++ [.ref (.func a), .callRefType fi.type] ++
        rest⟩) := by
    rw [← List.singleton_append, ← List.append_assoc]
    exact top _ rest (.call hx hfi)
  have hbT : b ≠ .taskReturn := by rintro rfl; simp [bi] at hbi
  have hn : (as.map w).length = ps.length := by rw [List.length_map, hlen, har hbT]
  have r₂ := HStep.host (Pf := Pf) (hb := hb) (ma := ma) (f := F) (c := .callRefType fi.type)
    (q := (s.st, s.rp)) trivial hfi hexp hn hcode hans
  have e₁ : stackA (as.map w).reverse = vals ((as.map w).map Val.i32) := by simp [stackA]
  have e₂ : stackA (res.map w).reverse = vals ((res.map w).map Val.i32) := by simp [stackA]
  rw [e₁] at r₁ ⊢
  rw [e₂]
  exact r₁.trans (.single (by simpa [vals] using hstep_ctx [] rest r₂))

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
