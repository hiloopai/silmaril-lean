module

public import Silmaril.Proofs.Wasm.Models.FXCoreSave.Run

/-!
# The restore code in Core 3.0

* `global?_module`, `recTy_module`, `setLocals_module`, `setLocals_length`: frames with the same
  module see the same globals and types;
* `loadLocals_run`: loading the locals `i, …, i + m - 1` from the head record;
* **`restore_run`**: from a buffer whose head record is `q`, the restore code sets the locals
  `0, …, n-1` to `q.locals`, stores `q.r` in the dispatch global and pops the record; the rest of
  the buffer stays a chain.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXCoreSave

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Models.FXCoreSave
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem global?_module {s : Store H} {f f' : Frame} (h : f'.module = f.module) (x : GlobalIdx) :
    s.global? f' x = s.global? f x := by
  simp only [Store.global?, h]

theorem recTy_module {f f' : Frame} (h : f'.module = f.module) {x : TypeIdx} {n : Nat}
    (hx : RecTy f x n) : RecTy f' x n := by
  obtain ⟨d, fs, hd, rest⟩ := hx
  exact ⟨d, fs, by simpa only [Frame.type?, h] using hd, rest⟩

theorem setLocals_module (f : Frame) :
    ∀ (ls : List Val) (i : Nat), (setLocals f ls i).module = f.module := by
  intro ls
  induction ls generalizing f with
  | nil => intro i; rfl
  | cons v vs ih => intro i; exact ih _ (i + 1)

theorem setLocals_length (f : Frame) :
    ∀ (ls : List Val) (i : Nat), (setLocals f ls i).locals.length = f.locals.length := by
  intro ls
  induction ls generalizing f with
  | nil => intro i; rfl
  | cons v vs ih =>
    intro i
    rw [setLocals, ih]
    simp only [Frame.setLocal, List.length_set]

theorem setLocals_append (f : Frame) (l₁ l₂ : List Val) :
    ∀ i, setLocals f (l₁ ++ l₂) i = setLocals (setLocals f l₁ i) l₂ (i + l₁.length) := by
  induction l₁ generalizing f with
  | nil => intro i; rfl
  | cons v vs ih =>
    intro i
    simp only [List.cons_append, setLocals, ih, List.length_cons]
    congr 1
    omega

/-- **Loading the locals `i, …, i + m - 1` from the head record.** -/
theorem loadLocals_run {s : Store H} {x : TypeIdx} {b : GlobalIdx} {n : Nat} {f : Frame}
    (hx : RecTy f x n) (h32 : n + 3 ≤ 2 ^ 32) {ab : Nat} {gb : GlobalInst}
    (hb : s.global? f b = some (ab, gb)) {a : Nat} (hv : gb.value = .ref (.struct a))
    {si : StructInst} (hs : s.structs[a]? = some si) {q : CRec} {nx : Val}
    (hf : si.fields = (q.fields nx).map .val) (hn : q.locals.length = n)
    (hloc : n ≤ f.locals.length) (rest : List Admin) :
    ∀ (m i : Nat) (f' : Frame), f'.module = f.module → f'.locals.length = f.locals.length →
      i + m ≤ n →
      Steps P host ⟨s, f', expression ((List.range' i m).map (loadLocal x b)).flatten ++ rest⟩
        ⟨s, setLocals f' ((q.locals.drop i).take m) i, rest⟩ := by
  intro m i f' hmod hlen hle
  induction m generalizing i f' with
  | zero =>
    simp only [List.range'_zero, List.map_nil, List.flatten_nil, expression, List.map_nil,
      List.nil_append, List.take_zero, setLocals]
    exact .refl
  | succ m ih =>
    show Steps P host
      ⟨s, f', expression ((List.range' i (m + 1)).map (loadLocal x b)).flatten ++ rest⟩
      ⟨s, setLocals f' ((q.locals.drop i).take (m + 1)) i, rest⟩
    let tl : List Admin :=
      expression ((List.range' (i + 1) m).map (loadLocal x b)).flatten ++ rest
    have hi : i < q.locals.length := by omega
    have hb' : s.global? f' b = some (ab, gb) := by rw [global?_module hmod]; exact hb
    have hx' : RecTy f' x n := recTy_module hmod hx
    have hfl : i < (q.fields nx).length := by simp [CRec.fields]; omega
    have hget : (q.fields nx)[i] = q.locals[i] := List.getElem_append_left hi
    have hix : (ix i : LocalIdx).toNat < f'.locals.length := by
      rw [ix_toNat (k := .local) (j := i) (by omega)]; omega
    have h1 : Step P host
        ⟨s, f', expression ((List.range' i (m + 1)).map (loadLocal x b)).flatten ++ rest⟩
        ⟨s, f', vals [] ++ [.ref (.struct a), .plain (.structGet none x (ix i))] ++
          ([.plain (.localSet (ix i))] ++ tl)⟩ :=
      step_eq (step_ctx [] ([.plain (.structGet none x (ix i)), .plain (.localSet (ix i))] ++ tl)
        (step_globalGet hb')) (by simp [List.range'_succ, loadLocal, expression, vals, tl])
        (by simp [vals, hv, Val.toAdmin])
    have h2 : Step P host
        ⟨s, f', vals [] ++ [.ref (.struct a), .plain (.structGet none x (ix i))] ++
          ([.plain (.localSet (ix i))] ++ tl)⟩
        ⟨s, f', vals [] ++ [q.locals[i].toAdmin, .plain (.localSet (ix i))] ++ tl⟩ :=
      step_eq (step_ctx [] ([.plain (.localSet (ix i))] ++ tl)
        (step_structGet hx' hs hf (i := i) (by omega) h32 hfl)) rfl (by simp [vals, hget])
    have h3 : Step P host
        ⟨s, f', vals [] ++ [q.locals[i].toAdmin, .plain (.localSet (ix i))] ++ tl⟩
        ⟨s, f'.setLocal (ix i) q.locals[i], tl⟩ :=
      step_eq (step_ctx [] tl (.variable (.localSet hix))) rfl (by simp [vals])
    have h4 : Steps P host ⟨s, f'.setLocal (ix i) q.locals[i], tl⟩
        ⟨s, setLocals f' ((q.locals.drop i).take (m + 1)) i, rest⟩ :=
      steps_eq (ih (i + 1) (f'.setLocal (ix i) q.locals[i]) hmod
        (by simp only [Frame.setLocal, List.length_set, hlen]) (by omega)) rfl
        (by rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, setLocals])
    exact (((Relation.ReflTransGen.single h1).tail h2).tail h3).trans h4

/-- **The restore code**, at a head record `q` stored at struct address `a` with next pointer
`nx`. -/
theorem restore_run_at {s : Store H} {f : Frame} {x : TypeIdx} {b g : GlobalIdx} {n : Nat}
    (hx : RecTy f x n) (h32 : n + 3 ≤ 2 ^ 32) {ab : Nat} {gb : GlobalInst}
    (hb : s.global? f b = some (ab, gb)) {ag : Nat} {gg : GlobalInst}
    (hg : s.global? f g = some (ag, gg)) (hne : ag ≠ ab) {a : Nat}
    (hvb : gb.value = .ref (.struct a)) {si : StructInst} (hs : s.structs[a]? = some si)
    {q : CRec} {nx : Val} (hf : si.fields = (q.fields nx).map .val) (hn : q.locals.length = n)
    (hloc : n ≤ f.locals.length) (rest : List Admin) :
    Steps P host ⟨s, f, expression (restoreCode x b g n) ++ rest⟩
      ⟨restoreStore s q nx ag ab, setLocals f q.locals 0, rest⟩ := by
  subst hn
  let n := q.locals.length
  let f₁ := setLocals f q.locals 0
  have hmod : f₁.module = f.module := setLocals_module f q.locals 0
  let t6 : List Instr := [.globalGet b, .structGet none x (ix (n + 1)), .globalSet g,
    .globalGet b, .structGet none x (ix (n + 2)), .globalSet b]
  -- the locals
  have h1 := loadLocals_run (P := P) (host := host) hx h32 hb hvb hs hf rfl hloc
    (expression t6 ++ rest) n 0 f rfl rfl (by omega)
  have e1 : (q.locals.drop 0).take n = q.locals := by simp [n]
  rw [e1] at h1
  have e0 : expression (restoreCode x b g n) ++ rest =
      expression ((List.range' 0 n).map (loadLocal x b)).flatten ++ (expression t6 ++ rest) := by
    simp [restoreCode, expression, t6, List.range_eq_range']
  -- the resume index
  have hb₁ : s.global? f₁ b = some (ab, gb) := by rw [global?_module hmod]; exact hb
  have hg₁ : s.global? f₁ g = some (ag, gg) := by rw [global?_module hmod]; exact hg
  have hx₁ := recTy_module hmod hx
  have hfl1 : n + 1 < (q.fields nx).length := by simp [CRec.fields, n]
  have hfl2 : n + 2 < (q.fields nx).length := by simp [CRec.fields, n]
  have hr : (q.fields nx)[n + 1] = .i32 q.r := by simp [CRec.fields, n]
  have hnx : (q.fields nx)[n + 2] = nx := by simp [CRec.fields, n]
  let t3 : List Admin := expression [.globalGet b, .structGet none x (ix (n + 2)), .globalSet b] ++
    rest
  have h2 := step_ctx [] ([.plain (.structGet none x (ix (n + 1))), .plain (.globalSet g)] ++ t3)
    (step_globalGet (P := P) (host := host) hb₁)
  have h3 := step_ctx [] ([.plain (.globalSet g)] ++ t3)
    (step_structGet (P := P) (host := host) hx₁ hs hf (i := n + 1) (by omega) h32 hfl1)
  have h4 := step_ctx [] t3 (step_globalSet (P := P) (host := host) hg₁ (.i32 q.r))
  have e2 : expression t6 ++ rest = vals [] ++ [.plain (.globalGet b)] ++
      ([.plain (.structGet none x (ix (n + 1))), .plain (.globalSet g)] ++ t3) := by
    simp [t6, t3, expression, vals]
  have e3 : vals [] ++ [gb.value.toAdmin] ++
      ([.plain (.structGet none x (ix (n + 1))), .plain (.globalSet g)] ++ t3) =
      vals [] ++ [.ref (.struct a), .plain (.structGet none x (ix (n + 1)))] ++
        ([.plain (.globalSet g)] ++ t3) := by
    simp [vals, hvb, Val.toAdmin]
  have e4 : vals [] ++ [(q.fields nx)[n + 1].toAdmin] ++ ([.plain (.globalSet g)] ++ t3) =
      vals [] ++ [(Val.i32 q.r).toAdmin, .plain (.globalSet g)] ++ t3 := by
    simp [vals, hr]
  have e5 : vals [] ++ ([] : List Admin) ++ t3 = t3 := by simp [vals]
  rw [e3] at h2
  rw [e4] at h3
  rw [e5] at h4
  -- pop the record
  let s₁ := s.setGlobal ag (.i32 q.r)
  have hb₂ : s₁.global? f₁ b = some (ab, gb) := global?_setGlobal_ne hb₁ hne _
  have hs₁ : s₁.structs[a]? = some si := by rw [structs_setGlobal]; exact hs
  have h5 := step_ctx [] ([.plain (.structGet none x (ix (n + 2))), .plain (.globalSet b)] ++ rest)
    (step_globalGet (P := P) (host := host) hb₂)
  have h6 := step_ctx [] ([.plain (.globalSet b)] ++ rest)
    (step_structGet (P := P) (host := host) (s := s₁) hx₁ hs₁ hf (i := n + 2) (by omega) h32 hfl2)
  have h7 := step_ctx [] rest (step_globalSet (P := P) (host := host) hb₂ nx)
  have e6 : t3 = vals [] ++ [.plain (.globalGet b)] ++
      ([.plain (.structGet none x (ix (n + 2))), .plain (.globalSet b)] ++ rest) := by
    simp [t3, expression, vals]
  have e7 : vals [] ++ [gb.value.toAdmin] ++
      ([.plain (.structGet none x (ix (n + 2))), .plain (.globalSet b)] ++ rest) =
      vals [] ++ [.ref (.struct a), .plain (.structGet none x (ix (n + 2)))] ++
        ([.plain (.globalSet b)] ++ rest) := by
    simp [vals, hvb, Val.toAdmin]
  have e8 : vals [] ++ [(q.fields nx)[n + 2].toAdmin] ++ ([.plain (.globalSet b)] ++ rest) =
      vals [] ++ [nx.toAdmin, .plain (.globalSet b)] ++ rest := by
    simp [vals, hnx]
  have e9 : vals [] ++ ([] : List Admin) ++ rest = rest := by simp [vals]
  rw [e7] at h5
  rw [e8] at h6
  rw [e9] at h7
  rw [e6] at h4
  rw [e0]
  rw [e2] at h1
  exact h1.trans ((((((Relation.ReflTransGen.single h2).tail h3).tail h4).tail h5).tail h6).tail h7)

/-- **The restore code**, at the head of a buffer: the rest of the buffer stays a chain. -/
theorem restore_run {s : Store H} {f : Frame} {x : TypeIdx} {b g : GlobalIdx} {n : Nat}
    (hx : RecTy f x n) (h32 : n + 3 ≤ 2 ^ 32) {ab : Nat} {gb : GlobalInst}
    (hb : s.global? f b = some (ab, gb)) {ag : Nat} {gg : GlobalInst}
    (hg : s.global? f g = some (ag, gg)) (hne : ag ≠ ab) {q : CRec} {qs : List CRec}
    (hbuf : BufIs s gb.value (q :: qs)) (hn : q.locals.length = n) (hloc : n ≤ f.locals.length)
    (rest : List Admin) :
    ∃ nx, BufIs (restoreStore s q nx ag ab) nx qs ∧
      Steps P host ⟨s, f, expression (restoreCode x b g n) ++ rest⟩
        ⟨restoreStore s q nx ag ab, setLocals f q.locals 0, rest⟩ := by
  generalize hvb : gb.value = v at hbuf
  cases hbuf with
  | @cons a si _ nx _ hs hf tl =>
    exact ⟨nx, bufIs_setGlobal _ _ (bufIs_setGlobal _ _ tl),
      restore_run_at hx h32 hb hg hne hvb hs hf hn hloc rest⟩

end Silmaril.Proofs.Wasm.Models.FXCoreSave
