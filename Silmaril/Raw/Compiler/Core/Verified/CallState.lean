module

public import Silmaril.Compiler.Core.Verified.StateProc.Defs
public import Silmaril.Compiler.Core.Verified.CallLink.Defs
/-! # Calls returning the value of a State block

A no-parameter callee may use the same local declarations, assignments and returning
conditionals as `State`. The emitted Lir contains a real call and computes the
symbolically substituted expression inside the callee.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CallState

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open ReturnLit (Eff NoBoundary ReturnLabel noBoundary_cons saveFree)
open ConvInt (isConvLoadedInt)
open IntExpr (Term)
open LocalExpr (Shows)
open StateMem (Fresh)
open Call (retKind callSite Gives compatible_reaches cfunction_reaches length_eval pureEval_of
  lookup_ext2_first lookup_ext2_second lookup_ext2_other)

variable {file : Program} {labels : Labels}

/-- A change of diagnostic location leaves the allocation reserve untouched. -/
theorem fresh_touched {m m' : Mem.Concrete.State} {ls : List StateMem.Local}
    (h : Fresh m ls) (t : LoadTask.Touched m m') : Fresh m' ls := by
  obtain ⟨l, u, rfl⟩ := t
  exact ⟨h.dead, h.ids, h.addrs, h.last⟩

/-- A known no-parameter `int` procedure with a State body. -/
def callee (file : File Codec.wireModel Unit Unit) (g : Sym) : Option Term :=
  if (file.stdlib.lookup g).isSome then none else
  match file.funInfo.lookup g, file.funs.lookup g with
  | some (_, _, rty, [], _, _), some (.procedure _ _ _ [] body) =>
    if retKind rty = some true then State.recognizeBody file body else none
  | _, _ => none

theorem callee_spec {g : Sym} {t : Term} (hc : callee file g = some t) :
    ∃ loc attrs rty variadic proto dloc marker bt body,
      file.stdlib.lookup g = none ∧
      file.funInfo.lookup g = some (loc, attrs, rty, [], variadic, proto) ∧
      file.funs.lookup g = some (.procedure dloc marker bt [] body) ∧ retKind rty = some true ∧
      State.recognizeBody file body = some t := by
  unfold callee at hc
  split at hc
  · cases hc
  rename_i hstd
  split at hc
  · rename_i loc attrs rty variadic proto dloc marker bt body hinfo hdecl
    split at hc
    · exact ⟨loc, attrs, rty, variadic, proto, dloc, marker, bt, body,
        by simpa using hstd, hinfo, hdecl, by assumption, hc⟩
    · cases hc
  · cases hc

theorem body_gives {body : EE} {t : Term} (hbody : State.recognizeBody file body = some t)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (fresh : Fresh m []) :
    Gives (file := file) (labels := labels)
      ⟨.effectExpr body env, .procedureReturn (CallReach.bodyLabels body) :: k, m⟩ k m.stdout (some t) := by
  rcases StateProc.body_returns (file := file) (labels := labels) hbody env k m (StateProc.Reserve.ofFresh fresh) with
    ⟨ok, m', out, r⟩ | ub
  · exact .inl ⟨ok, m', out, r.trans (CallReach.return_reaches _ _ k m')⟩
  · exact .inr ub

theorem call_gives {e : EE} {g : Sym} {t : Term}
    (hs : callSite file e = some (g, true)) (hc : callee file g = some t)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (fresh : Fresh m []) :
    Gives (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ k m.stdout (some t) := by
  obtain ⟨loc, attrs, fty, variadic, proto, dloc, marker, bt, body, hstd, hinfo, hdecl, hfk, hbody⟩ :=
    callee_spec hc
  unfold callSite at hs
  split at hs
  · rename_i ann pann p pbt fann vann g' lann tann fa fty' fbt pa pty pbt' w1a w1 w2a w2 cann cpann
      p₁ iann oann lenann len lnann pty₁ zann z iann' cpa cva rty cfa fty₁ ccann mt pann₂ p₂ no1 no2
    split at hs
    · rename_i cond
      obtain ⟨hp₁, hp₂, hpty, hfty, hne, hpf, hpp, rfl, hlen⟩ := cond
      have hrk : retKind rty = some true ∧ g' = g := by
        cases h : retKind rty with
        | none => simp [h] at hs
        | some b =>
          simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
          exact ⟨by rw [hs.2], hs.1⟩
      obtain ⟨hrk, rfl⟩ := hrk
      let fp : Val := .loaded (.specified (.pointer (.function g')))
      let env₁ := extendEnv [(p, fp)] env
      let env₂ := extendEnv [(fty', (.ctype fty : Val)), (pty, .list .ctype [])] env₁
      have l1 : env₁.lookup p₁ = some fp := ConvInt.lookup_one hp₁
      have l2 : env₂.lookup pty₁ = some (.list .ctype []) :=
        lookup_ext2_second hpty (fun h => hne h.symm)
      have l3 : env₂.lookup fty₁ = some (.ctype fty) := lookup_ext2_first hfty
      have l4 : env₂.lookup p₂ = some fp := by
        rw [lookup_ext2_other (by rw [hp₂]; exact hpf) (by rw [hp₂]; exact hpp)]
        exact ConvInt.lookup_one hp₂
      have hmatch : matchPattern (.mk tann (.ctor .tuple [.mk fa (.base (some fty', fbt)),
          .mk pa (.base (some pty, pbt')), .mk w1a (.base (none, w1)), .mk w2a (.base (none, w2))]))
          (.tuple [.ctype fty, .list .ctype (([] : List (Option Sym × Ctype)).map fun q => .ctype q.2),
            boolean variadic, boolean proto]) =
          some [(fty', .ctype fty), (pty, .list .ctype [])] := rfl
      let m₁ := SeqReach.focusMemory fann m
      let m₂ := SeqReach.focusMemory lann m₁
      let m₃ := SeqReach.focusMemory iann m₂
      let m₄ := SeqReach.focusMemory iann' m₃
      have o := body_gives (file := file) (labels := labels) hbody env₂ k (SeqReach.focusMemory ccann m₄)
        (fresh_touched fresh ((StateStmt.seqFocus_touched fann m).trans
          ((StateStmt.seqFocus_touched lann m₁).trans ((StateStmt.seqFocus_touched iann m₂).trans
            ((StateStmt.seqFocus_touched iann' m₃).trans (StateStmt.seqFocus_touched ccann m₄))))))
      have hst : (SeqReach.focusMemory ccann m₄).stdout = m.stdout := by simp [m₄, m₃, m₂, m₁]
      rw [hst] at o
      refine Gives.pre ?_ o
      refine (SeqReach.sseq_pure_reaches ann fann (pat := .mk pann (.base (some p, pbt))) (xs := [(p, fp)])
        (SeqReach.pure_value vann (.loaded (.specified (.pointer (.function g')))) env) rfl k m).trans ?_
      refine (SeqReach.effect_let_reaches lann (cfunction_reaches l1 hinfo) hmatch k m₁).trans ?_
      refine (SeqReach.effect_if_reaches iann true (pureEval_of (length_eval hlen l2)) k m₂).trans ?_
      refine (SeqReach.effect_if_reaches iann' true (compatible_reaches hrk hfk l3) k m₃).trans ?_
      exact CallReach.ccall_reaches ccann mt (SeqReach.pure_symbol pann₂ p₂ env₂ fp l4) .nil
        (CallReach.procedure_not_builtin hdecl) (CallReach.procedure_body hstd hdecl rfl) k m₄
    · cases hs
  · cases hs


def retCall (file : File Codec.wireModel Unit Unit) (ret : Sym) : Eff → Option (Sym × Term)
  | .mk _ (.sseq (.mk _ (.base (some u, _))) (.mk _ (.bound e))
      (.mk _ (.run () l [.mk _ () (.call (.sym s)
        [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))), .mk _ () (.sym u')])]))) =>
      if l.key = ret.key ∧ u'.key = u.key ∧ isConvLoadedInt file s = true then
        match callSite file e with
        | some (g, true) =>
          match callee file g with
          | some t => some (g, t)
          | _ => none
        | _ => none
      else none
  | .mk _ (.sseq (.mk _ (.base (none, _))) a _) => retCall file ret a
  | _ => none


theorem retCall_halts {ret : Sym} (hret : ReturnLabel labels ret) (e : EE) {g : Sym} {t : Term}
    (h : retCall file ret e = some (g, t)) (env : Env) {k : List Frame} (hk : NoBoundary k)
    (m : Mem.Concrete.State) (fresh : Fresh m []) :
    Shows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ 0 t m.stdout := by
  unfold retCall at h
  split at h
  · rename_i _ ann pann u ty bann e' rann l cann s a2 tyann a3 u'
    split at h
    · rename_i cond
      obtain ⟨hl, hu, hs⟩ := cond
      split at h
      · rename_i g' hsite
        split at h
        · rename_i t' hcallee
          cases h
          let R : EE := .mk rann (.run () l [.mk cann () (.call (.sym s)
            [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))), .mk a3 () (.sym u')])])
          let kR := Frame.strongBind (.mk pann (.base (some u, ty))) R env :: k
          have pre : Reaches file labels
              ⟨.effectExpr (.mk ann (.sseq (.mk pann (.base (some u, ty))) (.mk bann (.bound e')) R)) env,
                k, m⟩ ⟨.effectExpr e' env, .bound :: kR, m⟩ :=
            (ReturnConst.sequence_reaches file labels ann _ _ _ env k m).trans
              (ReturnLit.bound_reaches bann _ env _ m)
          refine LocalExpr.Shows.pre pre ?_
          rcases call_gives (labels := labels) hsite hcallee env (.bound :: kR) m fresh with
            ⟨ok, m₁, out₁, r⟩ | ⟨s', r, hs'⟩
          · left
            refine ⟨ok, ?_⟩
            let v : Val := IntExpr.spec (t.val 0)
            let env₁ := extendEnv [(u, v)] env
            have heval : Eval file (tagsOf file (ReturnConst.focusMemory rann m₁)) env₁
                (.inl (.mk cann () (.call (.sym s)
                  [.mk a2 () (.val (.ctype (.mk tyann (.basic (.integer (.signed .int)))))),
                    .mk a3 () (.sym u')])))
                (.inl v) :=
              ConvInt.convLoadedInt_eval (ann := tyann) hs
                (IntExpr.Term.ok_int ReturnExpr.isInt_zero t ok)
                (.cons .val (.cons (.sym (ConvInt.lookup_one hu)) .nil))
            obtain ⟨m', out, halts⟩ := ReturnLit.jump_halts hl hret v env₁ hk
              (ReturnConst.focusMemory rann m₁)
            refine ⟨m', by simp [out, out₁], ?_⟩
            refine r.trans ((LocalExpr.value_bound_reaches v kR m₁).trans ?_)
            refine (ReturnLit.bind_reaches pann u ty v R env k m₁).trans ?_
            refine (Straight.focus_reaches (m := m₁) Straight.request_run).trans ?_
            exact ((Eval.sound file _ heval) labels _ _ rfl).trans halts
          · exact .inr ⟨s', r, hs'⟩
        · cases h
      · cases h
    · cases h
  · rename_i _ ann pann ty a b
    exact LocalExpr.Shows.pre (ReturnConst.sequence_reaches file labels ann _ a b env k m)
      (retCall_halts hret a h env (k := .strongBind (.mk pann (.base (none, ty))) b env :: k)
        (noBoundary_cons hk trivial) m fresh)
  · cases h
termination_by sizeOf e


def recognizeBody (file : File Codec.wireModel Unit Unit) : Eff → Option Call.Plan
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
      if r'.key = r.key ∧ saveFree a = true then
        (retCall file ret a).map fun (g, t) => Call.Plan.ret g t
      else none
  | _ => none

/-- `main` calls a known procedure without parameters. -/
def recognize (doc : Codec.Document) : Option Call.Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body


theorem recognize_reaches (doc : Codec.Document) (pl : Call.Plan) (h : recognize doc = some pl)
    (enums : Map Sym IntegerType) (args : List String) :
    ∃ s labels, initial doc.file enums args = .ok (s, labels) ∧
      Shows (file := doc.file) (labels := labels) s 0 pl.result "" := by
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
          have hbody : recognizeBody doc.file body = some pl := by simpa [main, decl] using h
          have hdefs : ∀ x ∈ doc.file.globs, ∀ bt e, x.2 ≠ .definition bt e := by
            rintro ⟨x, g⟩ hx bt e rfl
            exact nodefs (List.any_eq_true.mpr ⟨_, hx, rfl⟩)
          obtain ⟨s, labels, m, xs, hinit, hout, hlast, hdead, hentry⟩ := StartupMem.initial_reaches_body_mem
            doc.file enums args hdefs main decl
          have hlabels : labels = Map.ofList (saves body).reverse := by
            simp [initial, main, decl] at hinit
            exact hinit.2.symm
          unfold recognizeBody at hbody
          split at hbody
          · rename_i ann pann bt0 a sann ret bt r info bann pann' r'
            split at hbody
            · rename_i cond
              obtain ⟨hr, hfree⟩ := cond
              have hret : ReturnLabel labels ret := by
                rw [hlabels]; exact ReturnLit.returnLabel_body hr hfree
              let SAVE : EE :=
                .mk sann (.save (ret, bt) [(r, info)] (.mk bann (.pure (.mk pann' () (.sym r')))))
              let k : List Frame := [.strongBind (.mk pann (.base (none, bt0))) SAVE ∅, .annotations xs]
              have hk : NoBoundary k := by simp [k, NoBoundary, hasBoundary]
              have o : Shows (file := doc.file) (labels := labels) ⟨.effectExpr a ∅, k, m⟩ 0
                  pl.result m.stdout := by
                cases hrc : retCall doc.file ret a with
                | none => simp [hrc] at hbody
                | some pair =>
                  obtain ⟨g, t⟩ := pair
                  simp only [hrc, Option.map_some, Option.some.injEq] at hbody
                  subst pl
                  exact retCall_halts hret a hrc ∅ hk m
                    ⟨hdead, by simp, by simp, by simp [hlast]⟩
              rw [hout] at o
              exact ⟨s, labels, hinit, LocalExpr.Shows.pre
                (hentry.trans (ReturnConst.sequence_reaches doc.file labels ann _ a SAVE ∅ _ m)) o⟩
            · cases hbody
          · cases hbody

/-- **Core side.** A recognised document reaches undefined behaviour, or exits with the value
of the returned expression mod 256 and no output. -/
theorem recognize_sound (doc : Codec.Document) (pl : Call.Plan) (h : recognize doc = some pl)
    (args : List String) :
    Spec.CoreUB doc args ∨ pl.result.Ok 0 ∧
      Spec.CoreBeh doc args (.exit (pl.result.val 0 % 256).toNat []) := by
  obtain ⟨s, labels, hinit, o⟩ :=
    recognize_reaches doc pl h (Map.ofList (doc.enumBindings.getD [])) args
  rcases o with ⟨ok, m', out, reach⟩ | ⟨s', reach, halt⟩
  · right
    refine ⟨ok, ?_⟩
    have beh := Spec.CoreBeh.exit (k := (pl.result.val 0 % 256).toNat) ⟨s, labels, hinit, reach⟩ rfl rfl
    simpa [Spec.coreBytes, out] using beh
  · left
    exact .inr ⟨s', _, _, ⟨s, labels, hinit, reach⟩, halt⟩


end Silmaril.Compile.Core.Verified.CallState
