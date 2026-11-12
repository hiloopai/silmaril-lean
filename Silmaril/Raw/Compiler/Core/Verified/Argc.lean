module

public import Silmaril.Compiler.Core.Verified.ArgvReloc.Defs
public import Silmaril.Compiler.Core.Verified.GlobalExpr.Defs

/-! # Returning an integer expression of `argc`

The Core parameter is an addressable startup object; its immutable integer slot
contains the argument count. The target receives that count in its entry register.
Only expressions reading this parameter are accepted; argv reads and writes are rejected.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Argc

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree)
open IntExpr (Term term)

/-- A return expression reading only the argc parameter, through sequencing glue. -/
def retTerm (file : File Codec.wireModel Unit Unit) (ret argc : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ ConvInt.isConvLoadedInt file s = true then
        term file argc e else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retTerm file ret argc a
  | _ => none

/-- The saved return label after a returning statement. -/
def bodyTerm (file : File Codec.wireModel Unit Unit) (argc : Sym) : Eff → Option Term
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then retTerm file ret argc a else none
  | _ => none

def recognize (doc : Codec.Document) : Option Term := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    if doc.file.callingConvention = .normal then do
      let s ← doc.file.main
      let .procedure _ _ _ [(argc, _), (argv, _)] body ← doc.file.funs.lookup s | none
      if argc.key ≠ argv.key then bodyTerm doc.file argc body else none
    else none

/-- The singleton-global return proof is independent of how the integer object was allocated. -/
theorem retTerm_global {file : Program} {ret argc : Sym} (e : EE) {t : Term}
    (h : retTerm file ret argc e = some t) (n : Int) :
    GlobalExpr.retTerm file ret [(argc, n)] e = some (argc, n, t) := by
  unfold retTerm at h
  split at h
  · rename_i _ ann pann u ty bann E rann l cann s a2 c3 a3 u'
    split at h
    · rename_i hc
      simp [GlobalExpr.retTerm, hc, GlobalExpr.pick, h]
    · cases h
  · rename_i _ ann pann ty a b
    simpa [GlobalExpr.retTerm] using retTerm_global a h n
  · cases h
termination_by sizeOf e

theorem argc_range {args : List String} (h : Spec.ArgsOk args) :
    Mem.Concrete.IntRange args.length := by
  have hr := ArgvReloc.room_of_argsOk h
  have hs : 0 ≤ StartupArgs.strRoom args := Int.natCast_nonneg _
  unfold Mem.Concrete.IntRange
  omega

/-- The normal calling convention passes pointers to the last two startup objects. -/
theorem paramValues_tail (qs : List Mem.Concrete.Pointer) (pa pc pv : Mem.Concrete.Pointer) :
    StartupArgs.paramValues (qs ++ [pa, pc, pv]) =
      [.object (.pointer pc), .object (.pointer pv)] := by
  simp only [StartupArgs.paramValues, List.length_append, List.length_cons, List.length_nil]
  rw [show qs.length + 3 - 2 = qs.length + 1 by omega, List.drop_append,
    List.drop_eq_nil_of_le (by omega), show qs.length + 1 - qs.length = 1 by omega]
  rfl

/-- A recognised argc expression reaches UB or returns its value for this argument vector. -/
theorem recognize_sound (doc : Codec.Document) (t : Term) (h : recognize doc = some t)
    (args : List String) (ha : Spec.ArgsOk args) :
    Spec.CoreUB doc args ∨ t.Ok args.length ∧
      Spec.CoreBeh doc args (.exit (t.val args.length % 256).toNat []) := by
  unfold recognize at h
  split at h
  · cases h
  rename_i nodefs
  split at h
  · rename_i normal
    cases main : doc.file.main with
    | none => simp [main] at h
    | some sym =>
      cases decl : doc.file.funs.lookup sym with
      | none => simp [main, decl] at h
      | some entry =>
        cases entry <;> try { simp [main, decl] at h }
        case procedure loc marker ty ps body =>
          cases ps with
          | nil => simp [main, decl] at h
          | cons p ps =>
            obtain ⟨argc, tc⟩ := p
            cases ps with
            | nil => simp [main, decl] at h
            | cons p ps =>
              obtain ⟨argv, tv⟩ := p
              cases ps with
              | cons p ps => simp [main, decl] at h
              | nil =>
                simp only [main, bind, Option.bind, decl] at h
                split at h
                · rename_i distinct
                  have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
                    rintro ⟨x, g⟩ hx bt e rfl
                    exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
                  obtain ⟨s, labels, xs, qs, B, pc, pv, m, hinit, hentry, hout, agree⟩ :=
                    ArgvReloc.initial_reaches_body_reloc doc.file (Map.ofList (doc.enumBindings.getD []))
                      args ha hdefs main decl normal 0
                  have hagree := agree (PureEval.tagsOf doc.file m) m (StartupArgs.Keeps.refl m)
                  obtain ⟨id, addr, hpc, slot⟩ := hagree.argcSlot
                  let env : Env := extendEnv [(argc, .object (.pointer pc)),
                    (argv, .object (.pointer pv))] ∅
                  have henv : extendEnv ([argc, argv].zip
                      (StartupArgs.paramValues (qs ++ [.allocated args.length B, pc, pv]))) ∅ = env := by
                    rw [paramValues_tail]; rfl
                  rw [henv] at hentry
                  have hx : env.lookup argc = some (.object (.pointer (.allocated id addr))) := by
                    rw [← hpc]; exact ConvInt.lookup_two_first rfl
                  have hlabels : labels = Map.ofList (saves body).reverse := by
                    simp [initial, main, decl] at hinit
                    exact hinit.2.symm
                  unfold bodyTerm at h
                  split at h
                  · rename_i _ ann pann bt0 a sann ret bt rr info bann pann' r'
                    split at h
                    · rename_i cond
                      obtain ⟨hr, hfree⟩ := cond
                      have hret : ReturnLabel labels ret := by
                        rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
                      let SAVE : EE := .mk sann (.save (ret, bt) [(rr, info)]
                        (.mk bann (.pure (.mk pann' () (.sym r')))))
                      let K : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE env,
                        .annotations xs]
                      have hK : NoBoundary K := by simp [K, NoBoundary, hasBoundary]
                      have pre := hentry.trans
                        (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE env _ m)
                      have shows := GlobalExpr.retTerm_halts (labels := labels) hret a
                        (retTerm_global a h (args.length : Int)) env hK m (by
                          intro x n hmem
                          simp only [List.mem_singleton, Prod.mk.injEq] at hmem
                          obtain ⟨rfl, rfl⟩ := hmem
                          exact ⟨argc_range ha, id, addr, hx, slot⟩)
                      rw [hout] at shows
                      rcases LocalExpr.Shows.pre pre shows with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
                      · refine .inr ⟨ok, ?_⟩
                        have beh := Spec.CoreBeh.exit (k := (t.val args.length % 256).toNat)
                          ⟨s, labels, hinit, reach⟩ rfl rfl
                        simpa [Spec.coreBytes, out] using beh
                      · exact .inl (.inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩)
                    · cases h
                  · cases h
                · cases h
  · cases h

end Silmaril.Compile.Core.Verified.Argc
