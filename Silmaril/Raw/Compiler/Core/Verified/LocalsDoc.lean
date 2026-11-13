module

public import Silmaril.Compiler.Core.Verified.LocalsStmt.Defs
public import Silmaril.Compiler.Core.Verified.OpsLink.Defs
public import Silmaril.Compiler.Core.Source.StartupMem.Defs

/-! # Documents whose `main` is one block with one `int` local

`recognize doc = some (n, r)`: `main` is a procedure without parameters, the file has no
global definitions, and `main`'s body is the block `{ int x = n; return x; }` (`r = none`)
or `{ int x = n; }` (`r = some d`, then `main` returns its return label's default `d`),
followed by the return label. `recognize_sound`: Core exits with `result n r mod 256` and no
output, for every argument list.

`ops n r` is the Lir translation of the block, the local in register 3: `r3 := n` (the
store), then `r0 := r3` (the load of `return x`) or `r0 := d` (the default return).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Locals

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Machine
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory focusMemory_stdout)
open ReturnLit (Eff NoBoundary ReturnLabel lookup_key saveFree noBoundary_cons)
open Mem.Concrete (LiveInt IntRange nextIntAddress)

variable {file : Program} {labels : Labels}

/-- `S1 ; S2` whose first statement is `return x;`. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret x : Sym) : Eff → Bool
  | .mk _ (.sseq (.mk _ (.base (none, _))) r _) => retLocal file ret x r
  | _ => false

/-- The block `{ int x = n; S }`: `n`, and whether `S` is `return x;` (else it is the end of
the block). -/
def block (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Int × Bool)
  | .mk _ (.sseq (.mk _ (.base (some x, _))) cr (.mk _ (.sseq (.mk _ (.base (none, _))) ini rest))) =>
      if createInt cr = true then
        (storeLit file x ini).bind fun n =>
          if retStmt file ret x rest = true then some (n, true)
          else if killUnit x rest = true then some (n, false) else none
      else none
  | _ => none

/-- The body of `main`: the block, then the return label `ret(r) = pure(r)` with its
default. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option (Int × Option Int)
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then
        match block file ret a with
        | some (n, true) => some (n, none)
        | some (n, false) =>
            (ReturnConst.recognizeBody
              (.mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann () (.sym r'))))))).map
              fun d => (n, some d)
        | none => none
      else none
  | _ => none

/-- `main` is one block with one `int` local. -/
def recognize (doc : Codec.Document) : Option (Int × Option Int) := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- The value `main` returns. -/
def result (n : Int) : Option Int → Int
  | none => n
  | some d => d

/-- The Lir translation of the block: the local lives in register 3. -/
def ops (n : Int) : Option Int → List (Lir.Op Mir.Reg)
  | none => [.const 3 (BitVec.ofInt 64 n), .move 0 3]
  | some d => [.const 3 (BitVec.ofInt 64 n), .const 0 (BitVec.ofInt 64 d)]

theorem ops_exec (n : Int) (r : Option Int) (fr0 : Lir.Frame Mir.Reg) (mem : Lir.Memory) :
    ∃ fr, Lir.execOps (ops n r) fr0 mem = some (fr, mem) ∧
      fr.get 0 = some (BitVec.ofInt 64 (result n r)) := by
  cases r <;> simp [ops, result, Lir.execOps, Lir.Op.exec]

/-! ## Core side -/

theorem retStmt_halts {ret x : Sym} {e : Eff} (h : retStmt file ret x e = true)
    (hret : ReturnLabel labels ret) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) {id addr n : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (hn : IntRange n)
    (slot : Slot m id addr n) :
    ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩ := by
  unfold retStmt at h
  split at h
  · rename_i _ ann pann ty r b
    obtain ⟨m', out, halts⟩ := retLocal_halts h hret env
      (k := .strongBind (.mk pann (.base (none, ty))) b env :: k) (noBoundary_cons hk trivial) m hx hn
      slot
    exact ⟨m', out, (ReturnConst.sequence_reaches file labels ann _ r b env k m).trans halts⟩
  · cases h

theorem block_reaches {ret : Sym} {e : Eff} {n : Int} {b : Bool}
    (h : block file ret e = some (n, b)) (hret : ReturnLabel labels ret) (env : Env)
    {k : List Frame} (hk : NoBoundary k) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    if b then ∃ m', m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.halt (.defined (.loaded (.specified (.integer n)))), [], m'⟩
    else ∃ m' xs, m'.stdout = m.stdout ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value .unit, .annotations xs :: k, m'⟩ := by
  unfold block at h
  split at h
  · rename_i _ ann pann x ty cr sann spann sty ini rest
    split at h
    · rename_i hcr
      cases hs : storeLit file x ini with
      | none => simp [hs] at h
      | some n' =>
        simp only [hs, Option.bind_some] at h
        let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
        let env₁ := extendEnv [(x, ptr)] env
        let B : EE := .mk sann (.sseq (.mk spann (.base (none, sty))) ini rest)
        obtain ⟨m₁, out₁, live₁, hcreate⟩ := createInt_reaches (file := file) (labels := labels) hcr
          env (.strongBind (.mk pann (.base (some x, ty))) B env :: k) m hpos hdead
        have hx₁ : env₁.lookup x = some ptr := ConvInt.lookup_one rfl
        obtain ⟨hn, m₂, xs, out₂, slot₂, hstore⟩ := storeLit_reaches (file := file) (labels := labels)
          hs env₁ (.strongBind (.mk spann (.base (none, sty))) rest env₁ :: k) m₁ hx₁ live₁
        have pre := (ReturnConst.sequence_reaches file labels ann (.mk pann (.base (some x, ty))) cr B
            env k m).trans (hcreate.trans ((ReturnLit.bind_reaches pann x ty ptr B env k m₁).trans
          ((ReturnConst.sequence_reaches file labels sann (.mk spann (.base (none, sty))) ini rest env₁ k
            m₁).trans (hstore.trans (annotations_bind_reaches xs spann sty .unit rest env₁ k m₂)))))
        have hk₂ : NoBoundary (.annotations xs :: k) := noBoundary_cons hk trivial
        split at h
        · rename_i hret'
          cases h
          obtain ⟨m', out, halts⟩ := retStmt_halts hret' hret env₁ hk₂ m₂ hx₁ hn slot₂
          exact ⟨m', by rw [out, out₂, out₁], pre.trans halts⟩
        · split at h
          · rename_i hkill
            cases h
            obtain ⟨m', out, hk'⟩ := killUnit_reaches hkill env₁ (.annotations xs :: k) m₂ hx₁
              slot₂.live
            exact ⟨m', xs, by rw [out, out₂, out₁], pre.trans hk'⟩
          · cases h
    · cases h
  · cases h

theorem errno_nextIntAddress {m : Mem.Concrete.State} (h : m.lastAddress = StartupReach.errnoAddr) :
    0 < nextIntAddress m := by
  simp only [nextIntAddress, h, StartupReach.errnoAddr]
  decide

/-- The whole-document run: the dynamics halts with `result n r` and empty stdout. -/
theorem recognize_reaches (doc : Codec.Document) (n : Int) (r : Option Int)
    (h : recognize doc = some (n, r)) (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels t, initial doc.file enums args = .ok (s, labels) ∧ Reaches doc.file labels s t ∧
      t.control = .halt (.defined (.loaded (.specified (.integer (result n r))))) ∧
      t.memory.stdout = "" := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  cases main : doc.file.main with
  | none => simp [main] at h
  | some sym =>
    cases decl : doc.file.funs.lookup sym with
    | none => simp [main, decl] at h
    | some entry =>
      cases entry <;> try { simp [main, decl] at h }
      case procedure loc marker ty ps body =>
        cases ps with
        | cons p ps => simp [main, decl] at h
        | nil =>
          have hbody : recognizeBody doc.file body = some (n, r) := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ :=
            StartupMem.initial_reaches_body_mem doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i _ ann pann bt0 a sann ret bt rr info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(rr, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              let K : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
              have hK : NoBoundary K := by simp [K, NoBoundary, hasBoundary]
              have pre := (hentry.trans
                (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m))
              cases hb : block doc.file ret a with
              | none => simp [hb] at hbody
              | some nb =>
                obtain ⟨n', b⟩ := nb
                have hrun := block_reaches (labels := labels) hb hret ∅ hK m (errno_nextIntAddress hlast)
                  (by simp [hdead])
                cases b with
                | true =>
                  simp only [hb] at hbody
                  cases hbody
                  obtain ⟨m', out, halts⟩ := hrun
                  exact ⟨s, labels, _, hinit, pre.trans halts, rfl, by simp [out, hout]⟩
                | false =>
                  simp only [hb] at hbody
                  cases hd : ReturnConst.recognizeBody SAVE with
                  | none => simp [SAVE, hd] at hbody
                  | some d =>
                    simp [SAVE, hd] at hbody
                    obtain ⟨rfl, rfl⟩ := hbody
                    obtain ⟨m₁, ys, out₁, hblock⟩ := hrun
                    obtain ⟨m₂, out₂, hsave⟩ := ReturnConst.recognizeBody_reaches doc.file labels SAVE d hd
                      ∅ [.annotations ys, .annotations xs] m₁
                    refine ⟨s, labels, ⟨.halt (.defined (.loaded (.specified (.integer d)))), [], m₂⟩,
                      hinit, pre.trans (hblock.trans ?_), rfl, ?_⟩
                    · refine (annotations_bind_reaches ys pann bt0 .unit SAVE ∅ _ m₁).trans
                        (hsave.trans ?_)
                      exact (annotations_merge_reaches ys xs _ [] m₂).trans
                        (ReturnConst.value_halts_annotations doc.file labels _ _ m₂)
                    · simp [out₂, out₁, hout]
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document exits with `result n r mod 256` and no output. -/
theorem recognize_sound (doc : Codec.Document) (n : Int) (r : Option Int)
    (h : recognize doc = some (n, r)) (args : List String) :
    Spec.CoreBeh doc args (.exit (result n r % 256).toNat []) := by
  obtain ⟨s, labels, t, hinit, reach, halt, out⟩ :=
    recognize_reaches doc n r h (Map.ofList (doc.enumBindings.getD [])) args
  have beh := Spec.CoreBeh.exit (k := (result n r % 256).toNat) ⟨s, labels, hinit, reach⟩ halt rfl
  simpa [Spec.coreBytes, out] using beh

end Silmaril.Compile.Core.Verified.Locals
