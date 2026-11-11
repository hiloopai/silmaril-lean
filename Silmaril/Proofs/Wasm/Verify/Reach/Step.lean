module

public import Silmaril.Proofs.Wasm.Verify.Reach.Families
public import Silmaril.Wasm.Execution.Core.Sim.SetFuncs

/-!
# Function reachability: preservation by every Core 3.0 step rule

`Step.cfgIn`: for every profile `P` and every host relation `host` that returns the store
unchanged with references into `G` (`HostIn G host`), a step `Step P host c c'` from a
configuration satisfying `CfgIn G fs` (with the function instances `FuncsClosed G fs`) leads to a
configuration satisfying `CfgIn G fs`, with the same function instances.

The proof is by induction on the step: the context rules use the induction hypothesis on the
sub-configuration, the call rules use `FuncsClosed` (the body of a called function in `G` names
only functions in `G`), and every other rule rearranges code, values and store contents that
satisfy the invariant already.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {G : Nat → Prop} {fs : List Nat} {Pl : Instr → Prop} {Bad : Nat → Prop}

/-! ## Elementwise reading of the code invariant -/

theorem CodeIn.label_iff {n : Nat} {cont : List Instr} {body : List Admin} :
    CodeIn G fs Pl [.label n cont body] ↔ (∀ i ∈ cont, PlOK Pl i) ∧ CodeIn G fs Pl body := by
  simp only [CodeIn, codeRefs_label, codeRefs_nil, List.append_nil, codeFrames_label,
    codeFrames_nil, codePlains_label, codePlains_nil, List.mem_append]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨fun i hi => h₃ i (.inl hi), h₁, h₂, fun i hi => h₃ i (.inr hi)⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    exact ⟨h₁, h₂, fun i hi => hi.elim (h₀ i) (h₃ i)⟩

theorem CodeIn.handler_iff {n : Nat} {cs : List Catch} {body : List Admin} :
    CodeIn G fs Pl [.handler n cs body] ↔ CodeIn G fs Pl body := by
  simp only [CodeIn, codeRefs_handler, codeRefs_nil, List.append_nil, codeFrames_handler,
    codeFrames_nil, codePlains_handler, codePlains_nil]

theorem CodeIn.frame_iff {n : Nat} {fi : Frame} {body : List Admin} :
    CodeIn G fs Pl [.frame n fi body] ↔ FrameIn G fs fi ∧ CodeIn G fs Pl body := by
  simp only [CodeIn, codeRefs_frame, codeRefs_nil, List.append_nil, codeFrames_frame,
    codeFrames_nil, codePlains_frame, codePlains_nil, List.mem_cons, forall_eq_or_imp]
  constructor
  · rintro ⟨h₁, ⟨hf, h₂⟩, h₃⟩
    exact ⟨hf, h₁, h₂, h₃⟩
  · rintro ⟨hf, h₁, h₂, h₃⟩
    exact ⟨h₁, ⟨hf, h₂⟩, h₃⟩

theorem CodeIn.expression {b : List Instr} (h : ∀ i ∈ b, PlOK Pl i) :
    CodeIn G fs Pl (expression b) :=
  ⟨by simp, by simp, by simpa using h⟩

theorem CodeIn.toAdmin {r : Result} (h : ∀ x ∈ codeRefs r.toAdmin, RefIn G x) :
    CodeIn G fs Pl r.toAdmin := by
  cases r with
  | values vs => exact CodeIn.ofVals fun x hx => h x (by simpa [Result.toAdmin] using hx)
  | throw a => exact CodeIn.cons (CodeIn.ref (by simp)) (CodeIn.plain rfl)
  | trap => exact CodeIn.trap

theorem retToCallIn_callees {c : Admin} (m : ModuleInst) (hc : c.IsReturnCallRef) :
    CodeIn G fs Pl [c.retToCallIn m] := by
  rcases c with ⟨_⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp_all only [Admin.IsReturnCallRef, Admin.retToCallIn]
  · rename_i i
    cases i <;> simp_all only
    split
    · exact ⟨by simp, by simp, by simp⟩
    · exact CodeIn.plain rfl
  · exact ⟨by simp, by simp, by simp⟩

/-! ## Rules with calls and frames -/

theorem FrameIn.forCall {m : ModuleInst} (hm : m.funcs = fs) {vs : List Val}
    (hvs : ∀ r, Val.ref r ∈ vs → RefIn G r) (ls : List ValType) :
    FrameIn G fs (Frame.forCall m vs ls) := by
  refine ⟨.inl hm, fun r hr => ?_⟩
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨v, hv, hv'⟩ | ⟨ty, -, hty⟩
  · exact hvs r (Option.some.inj hv' ▸ hv)
  · exact defaultVal?_ref hty ▸ refIn_null

/-- `call x`: the callee is named by the instruction, so it is in `G`, or it is a guarded call
of a function in `Bad`. -/
theorem cfgIn_call (hP : PlainOK G Bad fs Pl) {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
    {d : DefType} (hx : f.module.funcs[x.toNat]? = some a)
    (hc : CfgIn G fs Pl ⟨s, f, [.plain (.call x)]⟩) :
    CfgIn G fs Pl ⟨s, f, [.ref (.func a), .callRefType d]⟩ ∨
      BadStep Bad fs ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType d]⟩ := by
  have hi : Pl (.call x) := hc.2.2.plain_head.of_callee (x := _) (by simp [instrCallees]; rfl)
  rcases hP.call x a hi (hc.2.1.resolve hx) with ha | ha
  · exact .inl ⟨hc.1, hc.2.1,
      CodeIn.cons (CodeIn.ref (by simpa using ha)) ⟨by simp, by simp, by simp⟩⟩
  · exact .inr ⟨.top [] [], x, a, d, by simp [Ctx.fill, vals], by simp [Ctx.fill, vals],
      hc.2.1.resolve hx, ha⟩

/-- `return_call x`. -/
theorem cfgIn_returnCall (hP : PlainOK G Bad fs Pl) {s : Store H} {f : Frame} {x : FuncIdx}
    {a : Nat} {d : DefType} (hx : f.module.funcs[x.toNat]? = some a)
    (hc : CfgIn G fs Pl ⟨s, f, [.plain (.returnCall x)]⟩) :
    CfgIn G fs Pl ⟨s, f, [.ref (.func a), .returnCallRefType d]⟩ := by
  have hi : Pl (.returnCall x) := hc.2.2.plain_head.of_callee (x := _) (by simp [instrCallees]; rfl)
  have ha : G a := hP.returnCall x a hi (hc.2.1.resolve hx)
  exact ⟨hc.1, hc.2.1, CodeIn.cons (CodeIn.ref (by simpa using ha)) ⟨by simp, by simp, by simp⟩⟩

/-- `call_ref` of a Wasm function in `G`: the new frame belongs to the module with function list
`fs` and the body names only functions in `G`. -/
theorem cfgIn_callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {code : Func} {k : Nat} (hcl : FuncsClosed G fs Pl s.funcs)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    CfgIn G fs Pl ⟨s, f, [.frame k (Frame.forCall fi.module vs code.locals)
      [.label k [] (expression code.body)]]⟩ := by
  have hvs : ∀ r, Val.ref r ∈ vs → RefIn G r := CodeIn.vals_refs hc.2.2
  have ha : G a := by simpa using hc.2.2.ref_of_mem (r := .func a) (by simp)
  have hbody : fi.module.funcs = fs ∧ ∀ i ∈ code.body, PlOK Pl i := hcl a fi code ha hf hcode
  have hlabel : CodeIn G fs Pl [.label k [] (expression code.body)] :=
    CodeIn.label_iff.2 ⟨by simp, CodeIn.expression hbody.2⟩
  exact ⟨hc.1, hc.2.1, CodeIn.frame_iff.2 ⟨FrameIn.forCall hbody.1 hvs _, hlabel⟩⟩

/-- A host call returns the store unchanged with references in `G`. -/
theorem cfgIn_callRefHost {host : HostSemantics H} (hh : HostIn G host) {s s' : Store H}
    {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {h : H} {r : Result}
    (hhost : host h s vs (.returned s' r))
    (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.ref (.func a), c]⟩) :
    CfgIn G fs Pl ⟨s', f, r.toAdmin⟩ ∧ s'.funcs = s.funcs := by
  obtain ⟨rfl, hr⟩ := hh h s vs s' r hhost
  exact ⟨⟨hc.1, hc.2.1, CodeIn.toAdmin hr⟩, rfl⟩

theorem cfgIn_throw {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat}
    (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.plain (.throw x)]⟩) :
    CfgIn G fs Pl ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩ :=
  ⟨hc.1.addExn (CodeIn.vals_refs hc.2.2), hc.2.1,
    CodeIn.cons (CodeIn.ref (by simp)) (CodeIn.plain rfl)⟩

theorem cfgIn_catch {s : Store H} {f : Frame} {a : Nat} {e : ExnInst} {l l₀ : List Admin}
    (he : s.exns[a]? = some e) (hc : CfgIn G fs Pl ⟨s, f, l₀⟩) (hl : CodeIn G fs Pl l) :
    CfgIn G fs Pl ⟨s, f, vals e.fields ++ l⟩ :=
  ⟨hc.1, hc.2.1, CodeIn.vals_append (fun _ hr => hc.1.exn he hr) hl⟩

theorem CodeIn.plain_of_in {i : Instr} (h : PlOK Pl i) : CodeIn G fs Pl [.plain i] :=
  ⟨by simp, by simp, by simpa using h⟩

theorem CodeIn.last_plain {vs : List Val} {i : Instr} (h : CodeIn G fs Pl (vals vs ++ [.plain i])) :
    PlOK Pl i :=
  (CodeIn.append.1 h).2.plain_head

/-! ## Context rules -/

/-- What a step leads to: the invariant again, or a guarded call (`BadStep`); the function
instances do not change. -/
def StepPost (G : Nat → Prop) (fs : List Nat) (Pl : Instr → Prop) (Bad : Nat → Prop)
    (c c' : Config H) : Prop :=
  (CfgIn G fs Pl c' ∨ BadStep Bad fs c c') ∧ c'.store.funcs = c.store.funcs

theorem StepPost.of_cfgIn {c c' : Config H} (h : CfgIn G fs Pl c')
    (hf : c'.store.funcs = c.store.funcs) : StepPost G fs Pl Bad c c' :=
  ⟨.inl h, hf⟩

theorem cfgIn_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : CfgIn G fs Pl ⟨s, f, is⟩ → StepPost G fs Pl Bad ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    StepPost G fs Pl Bad ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have h₁ : CodeIn G fs Pl (vals vs ++ is) ∧ CodeIn G fs Pl rest := CodeIn.append.1 hc.2.2
  have h₂ : CodeIn G fs Pl (vals vs) ∧ CodeIn G fs Pl is := CodeIn.append.1 h₁.1
  obtain ⟨hi | ⟨E, x, a, d, he, he', hx, ha⟩, hfun⟩ := ih ⟨hc.1, hc.2.1, h₂.2⟩
  · exact ⟨.inl ⟨hi.1, hi.2.1, CodeIn.append.2 ⟨CodeIn.append.2 ⟨h₂.1, hi.2.2⟩, h₁.2⟩⟩, hfun⟩
  · cases he'
    refine ⟨.inr ⟨E.wrap vs rest, x, a, d, ?_, ?_, hx, ha⟩, hfun⟩
    · simp only [Ctx.fill_wrap, ← he]
    · simp only [Ctx.fill_wrap]

theorem cfgIn_ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr}
    {is is' : List Admin} (hc : CfgIn G fs Pl ⟨s, f, [.label n cont is]⟩)
    (ih : CfgIn G fs Pl ⟨s, f, is⟩ → StepPost G fs Pl Bad ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    StepPost G fs Pl Bad ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  have h₁ : (∀ i ∈ cont, PlOK Pl i) ∧ CodeIn G fs Pl is := CodeIn.label_iff.1 hc.2.2
  obtain ⟨hi | ⟨E, x, a, d, he, he', hx, ha⟩, hfun⟩ := ih ⟨hc.1, hc.2.1, h₁.2⟩
  · exact ⟨.inl ⟨hi.1, hi.2.1, CodeIn.label_iff.2 ⟨h₁.1, hi.2.2⟩⟩, hfun⟩
  · cases he'
    refine ⟨.inr ⟨.label [] n cont E [], x, a, d, ?_, ?_, hx, ha⟩, hfun⟩
    · simp [Ctx.fill, vals, ← he]
    · simp [Ctx.fill, vals]

theorem cfgIn_ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
    {is is' : List Admin} (hc : CfgIn G fs Pl ⟨s, f, [.handler n cs is]⟩)
    (ih : CfgIn G fs Pl ⟨s, f, is⟩ → StepPost G fs Pl Bad ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    StepPost G fs Pl Bad ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨hi | ⟨E, x, a, d, he, he', hx, ha⟩, hfun⟩ :=
    ih ⟨hc.1, hc.2.1, CodeIn.handler_iff.1 hc.2.2⟩
  · exact ⟨.inl ⟨hi.1, hi.2.1, CodeIn.handler_iff.2 hi.2.2⟩, hfun⟩
  · cases he'
    refine ⟨.inr ⟨.handler [] n cs E [], x, a, d, ?_, ?_, hx, ha⟩, hfun⟩
    · simp [Ctx.fill, vals, ← he]
    · simp [Ctx.fill, vals]

theorem cfgIn_ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (hc : CfgIn G fs Pl ⟨s, f, [.frame n fi is]⟩)
    (ih : CfgIn G fs Pl ⟨s, fi, is⟩ → StepPost G fs Pl Bad ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    StepPost G fs Pl Bad ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  have h₁ : FrameIn G fs fi ∧ CodeIn G fs Pl is := CodeIn.frame_iff.1 hc.2.2
  obtain ⟨hi | ⟨E, x, a, d, he, he', hx, ha⟩, hfun⟩ := ih ⟨hc.1, h₁.1, h₁.2⟩
  · exact ⟨.inl ⟨hi.1, hc.2.1, CodeIn.frame_iff.2 ⟨hi.2.1, hi.2.2⟩⟩, hfun⟩
  · cases he'
    refine ⟨.inr ⟨.frame [] n fi E [], x, a, d, ?_, ?_, hx, ha⟩, hfun⟩
    · simp [Ctx.fill, vals, ← he]
    · simp [Ctx.fill, vals]

/-! ## Structured instructions -/

theorem instrCallees_nil_of_mem {b : List Instr} (h : exprCallees b = []) {i : Instr}
    (hi : i ∈ b) : instrCallees i = [] :=
  List.eq_nil_iff_forall_not_mem.2 fun x hx => by
    have hx' : x ∈ exprCallees b := mem_exprCallees hi hx
    simp [h] at hx'

theorem PlOK.body {b : List Instr} {i₀ : Instr} (hcal : instrCallees i₀ = exprCallees b)
    (hP : Pl i₀ → ∀ i ∈ b, PlOK Pl i) (h : PlOK Pl i₀) : ∀ i ∈ b, PlOK Pl i := by
  rcases h with h | h
  · exact fun i hi => .inl (instrCallees_nil_of_mem (hcal ▸ h) hi)
  · exact hP h

theorem PlOK.block (hP : PlainOK G Bad fs Pl) {bt : BlockType} {b : List Instr}
    (h : PlOK Pl (.block bt b)) : ∀ i ∈ b, PlOK Pl i :=
  PlOK.body (by simp [instrCallees]) (hP.block bt b) h

theorem PlOK.loop (hP : PlainOK G Bad fs Pl) {bt : BlockType} {b : List Instr}
    (h : PlOK Pl (.loop bt b)) : ∀ i ∈ b, PlOK Pl i :=
  PlOK.body (by simp [instrCallees]) (hP.loop bt b) h

theorem PlOK.tryTable (hP : PlainOK G Bad fs Pl) {bt : BlockType} {cs : List Catch}
    {b : List Instr} (h : PlOK Pl (.tryTable bt cs b)) : ∀ i ∈ b, PlOK Pl i :=
  PlOK.body (by simp [instrCallees]) (hP.tryTable bt cs b) h

theorem PlOK.ifLeft (hP : PlainOK G Bad fs Pl) {bt : BlockType} {b₁ b₂ : List Instr}
    (h : PlOK Pl (.if_ bt b₁ b₂)) : PlOK Pl (.block bt b₁) := by
  rcases h with h | h
  · left
    simp only [instrCallees, List.append_eq_nil_iff] at h ⊢
    exact h.1
  · exact hP.ifLeft bt b₁ b₂ h

theorem PlOK.ifRight (hP : PlainOK G Bad fs Pl) {bt : BlockType} {b₁ b₂ : List Instr}
    (h : PlOK Pl (.if_ bt b₁ b₂)) : PlOK Pl (.block bt b₂) := by
  rcases h with h | h
  · left
    simp only [instrCallees, List.append_eq_nil_iff] at h ⊢
    exact h.2
  · exact hP.ifRight bt b₁ b₂ h

/-! ## Blocks -/

theorem cfgIn_block (hP : PlainOK G Bad fs Pl) {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType} {body : List Instr}
    {n : Nat} (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩) :
    CfgIn G fs Pl ⟨s, f, [.label n [] (vals vs ++ expression body)]⟩ :=
  ⟨hc.1, hc.2.1, CodeIn.label_iff.2 ⟨by simp, CodeIn.vals_append (CodeIn.vals_refs hc.2.2)
    (CodeIn.expression (hc.2.2.last_plain.block hP))⟩⟩

theorem cfgIn_loop (hP : PlainOK G Bad fs Pl) {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType} {body : List Instr}
    {n : Nat} (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩) :
    CfgIn G fs Pl ⟨s, f, [.label n [.loop bt body] (vals vs ++ expression body)]⟩ :=
  ⟨hc.1, hc.2.1, CodeIn.label_iff.2 ⟨by simpa using hc.2.2.last_plain,
    CodeIn.vals_append (CodeIn.vals_refs hc.2.2) (CodeIn.expression (hc.2.2.last_plain.loop hP))⟩⟩

theorem cfgIn_tryTable (hP : PlainOK G Bad fs Pl) {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType}
    {cs : List Catch} {body : List Instr} {n : Nat}
    (hc : CfgIn G fs Pl ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩) :
    CfgIn G fs Pl ⟨s, f, [.handler n cs [.label n [] (vals vs ++ expression body)]]⟩ :=
  ⟨hc.1, hc.2.1, CodeIn.handler_iff.2 (CodeIn.label_iff.2 ⟨by simp,
    CodeIn.vals_append (CodeIn.vals_refs hc.2.2)
      (CodeIn.expression (hc.2.2.last_plain.tryTable hP))⟩)⟩

/-- Leaving a label with its continuation: values of the body, then the continuation. -/
theorem cfgIn_brLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {body : List Admin} {vs : List Val} (hc : CfgIn G fs Pl ⟨s, f, [.label n cont body]⟩)
    (hvs : ∀ x ∈ vals vs, x ∈ body) : CfgIn G fs Pl ⟨s, f, vals vs ++ expression cont⟩ := by
  have h₁ : (∀ i ∈ cont, PlOK Pl i) ∧ CodeIn G fs Pl body := CodeIn.label_iff.1 hc.2.2
  exact ⟨hc.1, hc.2.1, CodeIn.append.2 ⟨h₁.2.subset hvs, CodeIn.expression h₁.1⟩⟩

/-- A result built from elements of a label, handler or frame body (and fresh source
instructions naming no function). -/
theorem cfgIn_body {s : Store H} {f : Frame} {body l : List Admin} (hb : CodeIn G fs Pl body)
    (hc : CfgIn G fs Pl ⟨s, f, l⟩) {out : List Admin}
    (h : ∀ x ∈ out, x ∈ body ∨ ∃ i, x = .plain i ∧ instrCallees i = []) :
    CfgIn G fs Pl ⟨s, f, out⟩ := by
  refine ⟨hc.1, hc.2.1, CodeIn.of_forall fun x hx => ?_⟩
  rcases h x hx with hx | ⟨i, rfl, hi⟩
  · exact hb.singleton_of_mem hx
  · exact CodeIn.plain hi

theorem cfgIn_returnFrame {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
    {c : Admin} {rest : List Admin} (hc' : c.IsReturnCallRef)
    (hc : CfgIn G fs Pl
      ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩) :
    CfgIn G fs Pl ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  have hb : CodeIn G fs Pl (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest) :=
    (CodeIn.frame_iff.1 hc.2.2).2
  have h₁ : CodeIn G fs Pl (vals vs ++ [.ref (.func a)]) := hb.subset (fun x hx => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; tauto)
  exact ⟨hc.1, hc.2.1, by
    simpa using CodeIn.append.2 ⟨h₁, retToCallIn_callees (G := G) (fs := fs) fi.module hc'⟩⟩

/-! ## The step theorem -/

set_option linter.unusedTactic false in
/-- **Every Core 3.0 step preserves the reachability invariant**, except a guarded call of a
function in `Bad` (every profile, every host that returns the store unchanged with references
in `G`). -/
theorem Step.cfgIn (hP : PlainOK G Bad fs Pl) {P : Profile} {host : HostSemantics H}
    (hh : HostIn G host) {c c' : Config H} (h : Step P host c c')
    (hcl : FuncsClosed G fs Pl c.store.funcs) (hc : CfgIn G fs Pl c) :
    StepPost G fs Pl Bad c c' := by
  induction h with
  | parametric h => exact .of_cfgIn ⟨hc.1, hc.2.1, ParametricStep.out h hc.2.2⟩ rfl
  | numeric h => exact .of_cfgIn ⟨hc.1, hc.2.1, CodeIn.of_out (NumericStep.out h)⟩ rfl
  | vector h => exact .of_cfgIn ⟨hc.1, hc.2.1, CodeIn.of_out (VectorStep.out h)⟩ rfl
  | «variable» h => exact .of_cfgIn (VariableStep.cfgIn h hc) (VariableStep.funcs_eq h)
  | table h => exact .of_cfgIn (TableStep.cfgIn h hc) (TableStep.funcs_eq h)
  | memory h => exact .of_cfgIn (MemoryStep.cfgIn h hc) (MemoryStep.funcs_eq h)
  | reference h => exact .of_cfgIn (RefStep.cfgIn hP h hc) (RefStep.funcs_eq h)
  | aggregate h => exact .of_cfgIn (AggregateStep.cfgIn h hc) (AggregateStep.funcs_eq h)
  | ctxtInstrs _ _ ih => exact cfgIn_ctxtInstrs hc (ih hcl)
  | ctxtLabel _ ih => exact cfgIn_ctxtLabel hc (ih hcl)
  | ctxtHandler _ ih => exact cfgIn_ctxtHandler hc (ih hcl)
  | ctxtFrame _ ih => exact cfgIn_ctxtFrame hc (ih hcl)
  | block => exact .of_cfgIn (cfgIn_block hP hc) rfl
  | loop => exact .of_cfgIn (cfgIn_loop hP hc) rfl
  | ifTrue =>
    exact .of_cfgIn ⟨hc.1, hc.2.1, CodeIn.plain_of_in (hc.2.2.tail.plain_head.ifLeft hP)⟩ rfl
  | ifFalse =>
    exact .of_cfgIn ⟨hc.1, hc.2.1, CodeIn.plain_of_in (hc.2.2.tail.plain_head.ifRight hP)⟩ rfl
  | labelVals =>
    exact .of_cfgIn (cfgIn_body (CodeIn.label_iff.1 hc.2.2).2 hc (fun x hx => .inl hx)) rfl
  | brLabelZero => exact .of_cfgIn (cfgIn_brLabel hc (by simp; tauto)) rfl
  | call hx _ => exact ⟨cfgIn_call hP hx hc, rfl⟩
  | callRefFunc _ hf _ _ hcode => exact .of_cfgIn (cfgIn_callRefFunc hcl hf hcode hc) rfl
  | callRefHost _ _ _ _ _ hhost =>
    obtain ⟨h₁, h₂⟩ := cfgIn_callRefHost hh hhost hc
    exact .of_cfgIn h₁ h₂
  | returnCall hx _ => exact .of_cfgIn (cfgIn_returnCall hP hx hc) rfl
  | returnCallRefFrameAddr hc' => exact .of_cfgIn (cfgIn_returnFrame hc' hc) rfl
  | throw => exact .of_cfgIn (cfgIn_throw hc) rfl
  | tryTable => exact .of_cfgIn (cfgIn_tryTable hP hc) rfl
  | throwRefHandlerCatch he => exact .of_cfgIn (cfgIn_catch he hc (CodeIn.plain rfl)) rfl
  | throwRefHandlerCatchRef he =>
    exact .of_cfgIn (cfgIn_catch he hc (CodeIn.cons (CodeIn.ref (by simp)) (CodeIn.plain rfl))) rfl
  | callRefHostDiv => exact .of_cfgIn hc rfl
  | throwRefHandlerNext =>
    exact .of_cfgIn ⟨hc.1, hc.2.1, CodeIn.handler_iff.2 (CodeIn.handler_iff.1 hc.2.2)⟩ rfl
  | _ =>
    refine .of_cfgIn ⟨hc.1, hc.2.1, ?_⟩ rfl
    first
      | (verify_code_tac hc.2.2; done)
      | (verify_code_tac (CodeIn.label_iff.1 hc.2.2).2; done)
      | (verify_code_tac (CodeIn.handler_iff.1 hc.2.2); done)
      | (verify_code_tac (CodeIn.frame_iff.1 hc.2.2).2; done)

/-- With no guarded calls (`Bad` empty), every step preserves the invariant. -/
theorem Step.cfgIn_of_empty (hP : PlainOK G (fun _ => False) fs Pl) {P : Profile}
    {host : HostSemantics H} (hh : HostIn G host) {c c' : Config H} (h : Step P host c c')
    (hcl : FuncsClosed G fs Pl c.store.funcs) (hc : CfgIn G fs Pl c) :
    CfgIn G fs Pl c' ∧ c'.store.funcs = c.store.funcs := by
  obtain ⟨hc' | ⟨_, _, _, _, _, _, _, hb⟩, hf⟩ := Step.cfgIn hP hh h hcl hc
  · exact ⟨hc', hf⟩
  · exact hb.elim

end Silmaril.Wasm.Verify
