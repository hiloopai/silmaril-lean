module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Main
public import Silmaril.Wasm.FX.Asyncify.Tool.Run.Defs
public import Silmaril.Wasm.Binary.Core.DecodeSound
public import Silmaril.Wasm.Binaryen.Exe.EncodeSound

/-!
# From modules and bytes to the machine programs

New proofs (moved from `Silmaril/Raw/Wasm/FX/Asyncify/Tool/Bytes.lean`; `asyncifyBytes_spec`
restyled through `asyncifyBytes_inv`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

theorem fnDefsEqb_sound : ∀ {a b : List FnDef}, fnDefsEqb a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [fnDefsEqb] at h
  | _ :: _, [], h => by simp [fnDefsEqb] at h
  | x :: xs, y :: ys, h => by
    simp only [fnDefsEqb, fnDefEqb, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    have hb := Silmaril.Wasm.Binaryen.Exe.instrsEqb_sound h4
    rw [fnDefsEqb_sound h5]
    cases x; cases y; simp_all

theorem envEqb_sound {a b : Env} (h : envEqb a b = true) : a = b := by
  simp only [envEqb, Bool.and_eq_true, beq_iff_eq] at h
  cases a; cases b
  simp only at h
  rw [h.1, fnDefsEqb_sound h.2]

/-- The recogniser returns a well-formed program whose machine program is the module's. -/
theorem recognize_sound {m : Module} {P : Prog} (h : recognize m = .ok P) :
    P.WF ∧ envOf m = some P.env := by
  unfold recognize at h
  cases hE : envOf m with
  | none => rw [hE] at h; cases h
  | some E =>
    rw [hE] at h
    simp only at h
    by_cases h1 : envEqb (progOf E).env E = true
    · by_cases h2 : (progOf E).wf = true
      · simp only [h1, h2, ↓reduceIte, Except.ok.injEq] at h
        subst h
        exact ⟨h2, by rw [envEqb_sound h1]⟩
      · simp [h1, h2] at h
    · simp [h1] at h

theorem asyncify_eq {m m' : Module} {pages : Nat} (h : asyncify m pages = .ok m') :
    ∃ P, recognize m = .ok P ∧ m' = asyncifyModule m P pages ∧
      P.sb + 4 * P.frameWords ≤ 65536 * pages := by
  unfold asyncify at h
  cases hr : recognize m with
  | error e => rw [hr] at h; cases h
  | ok P =>
    rw [hr] at h
    simp only at h
    refine ⟨P, rfl, ?_⟩
    by_cases h1 : (m.exports.any fun e => e.name == stateExport || e.name == memoryExport) = true
    · simp [h1] at h
    · by_cases h2 : P.sb + 4 * P.frameWords ≤ 65536 * pages ∧ pages < 65536
      · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq, and_self] at h
        subst h; exact ⟨rfl, h2.1⟩
      · simp [h1, h2] at h

theorem envOf_parts {m : Module} {E : Env} (h : envOf m = some E) :
    plainModule m = true ∧ m.imports.mapM (impSig m) = some E.imps ∧
      m.funcs.mapM (fnDefOf m) = some E.fns := by
  unfold envOf at h
  by_cases hp : plainModule m = true
  · simp only [hp, ↓reduceIte] at h
    cases hi : m.imports.mapM (impSig m) with
    | none => rw [hi] at h; cases h
    | some imps =>
      cases hf : m.funcs.mapM (fnDefOf m) with
      | none => rw [hi, hf] at h; cases h
      | some fns =>
        rw [hi, hf] at h
        cases h
        exact ⟨hp, rfl, rfl⟩
  · simp [hp] at h

theorem i32Sig_async (m : Module) (P : Prog) (pages : Nat) (t : TypeIdx) :
    i32Sig (asyncifyModule m P pages) t = i32Sig m t := rfl

theorem impSig_async (m : Module) (P : Prog) (pages : Nat) (im : Import) :
    impSig (asyncifyModule m P pages) im = impSig m im := rfl

theorem filter_funcs_of_mapM {m : Module} {l : List Import} {imps : List (Nat × Nat)}
    (h : l.mapM (impSig m) = some imps) :
    l.filter isFuncImport = l := by
  rw [List.mapM_eq_some_iff_forall₂] at h
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    rename_i im _ _ _
    rw [List.filter_cons, ih]
    unfold impSig at hab
    split at hab
    · rename_i _ _ heq; simp [isFuncImport, heq]
    · cases hab

theorem fns_async {m : Module} {P : Prog} :
    ∀ {fs : List Func} {fns : List FnSrc},
      List.Forall₂ (fun f d => fnDefOf m f = some d) fs
        (fns.map fun fn => (⟨fn.nparams, fn.nlocals, fn.nres, fn.body⟩ : FnDef)) →
      List.Forall₂ (fun f d => fnDefOf m f = some d)
        ((fs.zip fns).map fun (f, fn) => (⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32,
          P.tBody fn⟩ : Func))
        (fns.map fun fn => (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ : FnDef))
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | f :: fs, fn :: fns, h => by
    simp only [List.map_cons, List.forall₂_cons] at h
    obtain ⟨h1, h2⟩ := h
    simp only [List.zip_cons_cons, List.map_cons, List.forall₂_cons]
    refine ⟨?_, fns_async h2⟩
    unfold fnDefOf at h1 ⊢
    cases hs : i32Sig m f.type with
    | none => rw [hs] at h1; cases h1
    | some nr =>
      obtain ⟨n, r⟩ := nr
      rw [hs] at h1
      simp only at h1
      split at h1
      · rename_i hl
        simp only [Option.some.injEq, FnDef.mk.injEq] at h1
        obtain ⟨hn, -, hr, -⟩ := h1
        subst hn hr
        simp
      · cases h1

/-- The output module, read back by the lax reader, is the machine program of the pass. -/
theorem envOfLax_asyncifyModule {m : Module} {P : Prog} (h : envOf m = some P.env) (pages : Nat) :
    envOfLax (asyncifyModule m P pages) = some (asyncifyProg P) := by
  obtain ⟨-, hi, hf⟩ := envOf_parts h
  have hfil := filter_funcs_of_mapM hi
  have hf' := (List.mapM_eq_some_iff_forall₂).1 hf
  have hfns := fns_async (P := P) hf'
  have hfns' : ((m.funcs.zip P.fns).map fun (f, fn) => (⟨f.type, List.replicate (P.frameWords -
      fn.nparams) .i32, P.tBody fn⟩ : Func)).mapM (fnDefOf (asyncifyModule m P pages)) =
      some (P.fns.map fun fn => (⟨fn.nparams, P.frameWords - fn.nparams, fn.nres, P.tBody fn⟩ : FnDef)) :=
    (List.mapM_eq_some_iff_forall₂).2 hfns
  have hI : (asyncifyModule m P pages).imports = m.imports := rfl
  have hF : (asyncifyModule m P pages).funcs = (m.funcs.zip P.fns).map fun (f, fn) =>
      (⟨f.type, List.replicate (P.frameWords - fn.nparams) .i32, P.tBody fn⟩ : Func) := rfl
  have hi' : m.imports.mapM (impSig (asyncifyModule m P pages)) = some P.imps := hi
  unfold envOfLax
  rw [hI, hfil, hi', hF, hfns']
  rfl

theorem globalsOfLax_asyncifyModule (m : Module) (P : Prog) (pages : Nat) :
    globalsOfLax (asyncifyModule m P pages) = some P.tGlobals := rfl

theorem exportFunc_asyncifyModule (m : Module) (P : Prog) (pages : Nat) (name : String) :
    exportFunc (asyncifyModule m P pages) name = exportFunc m name := by
  simp [exportFunc, asyncifyModule, List.findSome?_append]

/-- The three stages of `asyncifyBytes`: decode, transform, encode. -/
theorem asyncifyBytes_inv {b b' : ByteArray} {pages : Nat} (h : asyncifyBytes b pages = .ok b') :
    ∃ m m' bs, Binary.Core.decode? b = some m ∧ asyncify m pages = .ok m' ∧
      Binaryen.Exe.encodeModule? m' = .ok bs ∧ b' = ⟨bs.toArray⟩ := by
  unfold asyncifyBytes at h
  split at h
  · cases h
  · rename_i m hd
    split at h
    · cases h
    · rename_i m' ha
      split at h
      · rename_i bs he
        exact ⟨m, m', bs, hd, ha, he, (Except.ok.inj h).symm⟩
      · cases h

/-- **The tool on bytes.** When `asyncifyBytes` succeeds, the input decodes (soundly, for the
binary grammar) to a module of the fragment with a well-formed source program `P`, and the
output bytes encode (for the same grammar) a module whose machine program is
`asyncifyProg P`, with the initial globals of the protocol and the same exported functions. -/
theorem asyncifyBytes_spec {b b' : ByteArray} {pages : Nat} (h : asyncifyBytes b pages = .ok b') :
    ∃ m P m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b.data.toList m ∧
      P.WF ∧ envOf m = some P.env ∧ m' = asyncifyModule m P pages ∧
      Binary.Core.Encodes b'.data.toList m' ∧ envOfLax m' = some (asyncifyProg P) ∧
      globalsOfLax m' = some P.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) := by
  obtain ⟨m, m', bs, hd, ha, he, hb'⟩ := asyncifyBytes_inv h
  obtain ⟨P, hr, hm', -⟩ := asyncify_eq ha
  obtain ⟨hwf, henv⟩ := recognize_sound hr
  have henc : Binary.Core.Encodes b'.data.toList m' := by
    rw [hb']; simpa using Binaryen.Exe.encodeModule?_sound he
  refine ⟨m, P, m', hd, Binary.Core.decode?_sound hd, hwf, henv, hm', henc, ?_, ?_, ?_⟩
  · rw [hm']; exact envOfLax_asyncifyModule henv pages
  · rw [hm']; exact globalsOfLax_asyncifyModule m P pages
  · rw [hm']; exact exportFunc_asyncifyModule m P pages

/-- **End to end.** When `wasm-asyncify asyncify` turns bytes `b` into bytes `b'`, the input
decodes to a module `m` of the fragment (source program `P`) and `b'` encodes a module `m'` read
back as `asyncifyProg P`, with the protocol's globals and the same exported functions; and for
every defined function `e`, argument list of the right length, deterministic host and source run
keeping the shadow stack inside the 32-bit address space, the call in `m` under the suspending
semantics and the same call in `m'` under the asyncify host protocol have the same behaviours. -/
theorem asyncifyBytes_correct {b b' : ByteArray} {pages : Nat} (h : asyncifyBytes b pages = .ok b') :
    ∃ m P m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b'.data.toList m' ∧
      envOf m = some P.env ∧ envOfLax m' = some (asyncifyProg P) ∧
      globalsOfLax m' = some P.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) ∧
      ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
        P.fnAt e = some fn → args.length = fn.nparams → DepthBound P H (srcCfg e fn args, s) →
        srcInit P.env e args = some (srcCfg e fn args) ∧
        tgtInit P e args s = some (tgtSt P e fn args s) ∧
        beh (srcStep P.env H) (srcCfg e fn args, s) =
          beh (tgtStep (asyncifyProg P) H) (tgtSt P e fn args s) := by
  obtain ⟨m, P, m', hd, -, hwf, henv, -, he, hlax, hgl, hex⟩ := asyncifyBytes_spec h
  exact ⟨m, P, m', hd, he, henv, hlax, hgl, hex, fun {_} H {_} {_} args s hfn hargs hb =>
    ⟨srcInit_eq hfn args, tgtInit_eq hfn args s, asyncify_beh P hwf H hfn args hargs s hb⟩⟩

end Silmaril.Wasm.FX.Asyncify.Tool
