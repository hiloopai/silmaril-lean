module

public import Silmaril.Wasm.Execution.Core.Typing.Store
public import Silmaril.Wasm.Execution.Core.Step
public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.Subtyping.WeakenEmpty

@[expose] public section

/-! # Configuration typing (§7.1 "Administrative instructions", "Configurations")

`Instr_ok2` (8 rules), `Instrs_ok2` (4 rules), `Expr_ok2`, `Localval_ok`,
`Frame_ok`, `State_ok`, `Config_ok`.

`AdminOk` transcribes `Instr_ok2`; source instructions are typed by `InstrOk`
(`Instr_ok2/plain`).

Deviation (documented): the spec's `Instrs_ok2/seq` only has a *single*
instruction on the left (`instr_1 instr_2*`) and there is no `Instrs_ok2/instr`.
With `frame` applying only to whole suffixes, that system is incomplete: an
instruction can never consume a value produced *before* the preceding
instruction (e.g. `i32.const 1; i32.const 2; drop; drop` has no typing, since
the second `drop` would need the tail `[drop]` typed with no parameters).
`AdminsOk` therefore follows the source `Instrs_ok` rules of §2.3 instead
(as `InstrsOk` does): `empty`, `instr` (`single`), `seq` with arbitrary
sequences on both sides, `sub` and `frame`; the spec's one-instruction
`Instrs_ok2/seq` is kept as the convenience constructor `cons`.

Deviation (documented): in `Instr_ok2/frame` the spec requires `C'.RETURN = t^n`
for the context `C'` produced by `Frame_ok`, but `Frame_ok` never sets `RETURN`,
so no frame would be typable. We type the body in `C'` *with* `RETURN (t^n)`,
which is the evident intent (and what the prose spec says).

Deviation (documented): the runtime annotations `CALL_REF deftype` and
`RETURN_CALL_REF deftype` (`AdminOk.callRefType`/`returnCallRefType`) require the
defined type to be valid in `{}` rather than in `C`. They are only produced by
`call`/`return_call`/`$invoke` from a store function type, which is closed.
Validity in a frame context `C` does not by itself give validity in `{}`: a type
valid in `C` may refer to `C.types` by index (`TyOk.idx`), and historically
SpecTec's `Moduleinst_ok` also leaves `RECS` unconstrained (which `ModuleInstOk`
now fixes to `[]`). That would break preservation of `call_ref` into a new frame.
Validity in `C` follows by `TyOk.of_empty`.

Deviation (documented): `Instr_ok2/trap` and (via the extra constructor
`AdminOk.throwRefInits`) the administrative `THROW_REF` may be typed with an arbitrary
list of in-bounds initialised locals, where the spec only allows none. Without it,
`trap-instrs`/`throw_ref-instrs` do not preserve types: with a non-defaultable local `x`
unset in the frame, `TRAP; LOCAL.SET x` is typed at `[] ->_{x} []`, but the reduct `TRAP`
(resp. `REF.EXN_ADDR a; THROW_REF`) has no typing initialising `x`, and subsumption
can only add set locals. Both instructions are divergent, so claiming extra
initialised locals is sound.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation

variable {H : Type}

/-- `Localval_ok`. -/
inductive LocalValOk (s : Store H) : Option Val → LocalType → Prop where
  | set {v : Val} {t : CValType} (h : ValOk s v t) : LocalValOk s (some v) ⟨.set, t⟩
  | unset {t : CValType} (h : TyOk {} t) : LocalValOk s none ⟨.unset, t⟩

/-- `Frame_ok: s ⊢ frame : C ++ {LOCALS lct*}`. -/
def FrameOk (s : Store H) (f : Frame) (C : Context) : Prop :=
  ∃ C₀ lts, ModuleInstOk s f.module C₀ ∧ List.Forall₂ (LocalValOk s) f.locals lts ∧
    C = { C₀ with locals := C₀.locals ++ lts }

mutual

/-- `Instr_ok2: s; C ⊢ instr : instrtype`. -/
inductive AdminOk (s : Store H) : Context → Admin → InstrType → Prop where
  /-- `Instr_ok2/plain`. -/
  | plain {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) :
      AdminOk s C (.plain i) it
  /-- `Instr_ok2/call_ref` (runtime defined-type annotation). Deviation: the
  annotation is valid in `{}` (not just in `C`), see the module doc. -/
  | callRefType {C : Context} {d : DefType} {ps rs : Ty (.list .val)}
      (hok : TyOk {} d) (he : Expand d (.func ps rs)) :
      AdminOk s C (.callRefType d) (.plain (ps.toList ++ [.refT true (.defHeap d)]) rs.toList)
  /-- `Instr_ok2/return_call_ref`. Deviation: the annotation is valid in `{}`. -/
  | returnCallRefType {C : Context} {d : DefType} {ps rs : Ty (.list .val)}
      {rs' t₃ t₄ : List CValType}
      (hok : TyOk {} d) (he : Expand d (.func ps rs))
      (hr : C.return_ = some rs') (hs : ResultSub C.toTypeCtx rs.toList rs')
      (hit : InstrTypeOk C (.plain t₃ t₄)) :
      AdminOk s C (.returnCallRefType d) (.plain (t₃ ++ ps.toList ++ [.refT true (.defHeap d)]) t₄)
  /-- `Instr_ok2/ref`. -/
  | ref {C : Context} {r : Ref} {rt : CRefType} (h : RefOk s r rt) :
      AdminOk s C (.ref r) (.plain [] [.refv rt])
  /-- `Instr_ok2/label`. -/
  | label {C : Context} {n : Nat} {cont : List Instr} {body : List Admin}
      {t' ts : List CValType} {xs' xs : List Nat}
      (hn : t'.length = n)
      (hc : AdminsOk s C (expression cont) ⟨t', xs', ts⟩)
      (hb : AdminsOk s (C.withLabel t') body ⟨[], xs, ts⟩) :
      AdminOk s C (.label n cont body) (.plain [] ts)
  /-- `Instr_ok2/frame` (see the module doc for `RETURN`). -/
  | frame {C C' : Context} {n : Nat} {fr : Frame} {body : List Admin} {ts : List CValType}
      (hf : FrameOk s fr C') (hn : ts.length = n)
      (hb : AdminsOk s { C' with return_ := some ts } body (.plain [] ts))
      (hok : ResultOk {} ts) :
      AdminOk s C (.frame n fr body) (.plain [] ts)
  /-- `Instr_ok2/handler`. -/
  | handler {C : Context} {n : Nat} {cs : List Catch} {body : List Admin} {ts : List CValType}
      {xs : List Nat} (hc : ∀ c ∈ cs, CatchOk C c) (hb : AdminsOk s C body ⟨[], xs, ts⟩) :
      AdminOk s C (.handler n cs body) (.plain [] ts)
  /-- `Instr_ok2/trap`. Deviation: `trap` may be typed with arbitrary (in-bounds)
  initialised locals `xs` (the spec only allows `[]`), so that `trap-instrs` preserves
  types when the discarded code initialises locals (see the module doc). -/
  | trap {C : Context} {t₁ t₂ : List CValType} {xs : List Nat}
      (hok : InstrTypeOk C ⟨t₁, xs, t₂⟩) :
      AdminOk s C .trap ⟨t₁, xs, t₂⟩
  /-- Deviation: administrative `throw_ref` typing with arbitrary (in-bounds) initialised
  locals (`Instr_ok/throw_ref` only allows `[]`), so that `throw_ref-instrs` preserves
  types when the discarded code initialises locals (see the module doc). -/
  | throwRefInits {C : Context} {t₁ t₂ : List CValType} {xs : List Nat}
      (hok : InstrTypeOk C ⟨t₁ ++ [.refT true (.abs .exn)], xs, t₂⟩) :
      AdminOk s C (.plain .throwRef) ⟨t₁ ++ [.refT true (.abs .exn)], xs, t₂⟩

/-- `Instrs_ok2: s; C ⊢ instr* : instrtype`. -/
inductive AdminsOk (s : Store H) : Context → List Admin → InstrType → Prop where
  /-- `Instrs_ok2/empty`. -/
  | nil {C : Context} : AdminsOk s C [] (.plain [] [])
  /-- `Instrs_ok/instr` (see the module doc). -/
  | single {C : Context} {a : Admin} {it : InstrType} (h : AdminOk s C a it) :
      AdminsOk s C [a] it
  /-- `Instrs_ok/seq` (general form; see the module doc). -/
  | seq {C : Context} {as₁ as₂ : List Admin} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}
      (h₁ : AdminsOk s C as₁ ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (h₂ : AdminsOk s (C.initLocals xs₁) as₂ ⟨t₂, xs₂, t₃⟩) :
      AdminsOk s C (as₁ ++ as₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩
  /-- `Instrs_ok2/seq` (one instruction on the left; derivable from `single`/`seq`). -/
  | cons {C : Context} {a : Admin} {as : List Admin} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}
      (ha : AdminOk s C a ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (hs : AdminsOk s (C.initLocals xs₁) as ⟨t₂, xs₂, t₃⟩) :
      AdminsOk s C (a :: as) ⟨t₁, xs₁ ++ xs₂, t₃⟩
  /-- `Instrs_ok2/sub`. -/
  | sub {C : Context} {as : List Admin} {it it' : InstrType}
      (h : AdminsOk s C as it) (hs : InstrTypeSub C it it') (hok : InstrTypeOk C it') :
      AdminsOk s C as it'
  /-- `Instrs_ok2/frame`. -/
  | frame {C : Context} {as : List Admin} {ts t₁ t₂ : List CValType} {xs : List Nat}
      (h : AdminsOk s C as ⟨t₁, xs, t₂⟩) (hok : ResultOk C.toTypeCtx ts) :
      AdminsOk s C as ⟨ts ++ t₁, xs, ts ++ t₂⟩

end

/-- `State_ok`. -/
def StateOk (s : Store H) (f : Frame) (C : Context) : Prop := StoreOk s ∧ FrameOk s f C

/-- `Config_ok: ⊢ config : t*`. -/
def ConfigOk (c : Config H) (ts : List CValType) : Prop :=
  ∃ C, StateOk c.store c.frame C ∧ AdminsOk c.store C c.code (.plain [] ts)

/-! ## Store extension -/

theorem LocalValOk.extend {s s' : Store H} {v : Option Val} {lt : LocalType} (he : Extend s s')
    (h : LocalValOk s v lt) : LocalValOk s' v lt := by
  cases h with
  | set h => exact .set (h.extend he)
  | unset h => exact .unset h

theorem FrameOk.extend_of_storeOk {s s' : Store H} {f : Frame} {C : Context} (hs : StoreOk s)
    (he : Extend s s') (h : FrameOk s f C) : FrameOk s' f C := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := h
  exact ⟨C₀, lts, hm.extend hs he, hl.imp fun _ _ h => h.extend he, rfl⟩

mutual

theorem AdminOk.extend_aux {s s' : Store H} (hS : StoreOk s) (he : Extend s s') :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → AdminOk s' C a it
  | _, _, _, .plain h => .plain h
  | _, _, _, .callRefType hok hex => .callRefType hok hex
  | _, _, _, .returnCallRefType hok hex hr hsub hit => .returnCallRefType hok hex hr hsub hit
  | _, _, _, .ref h => .ref (h.extend he)
  | _, _, _, .label hn hc hb =>
    .label hn (AdminsOk.extend_aux hS he hc) (AdminsOk.extend_aux hS he hb)
  | _, _, _, .frame hf hn hb hok =>
    .frame (hf.extend_of_storeOk hS he) hn (AdminsOk.extend_aux hS he hb) hok
  | _, _, _, .handler hc hb => .handler hc (AdminsOk.extend_aux hS he hb)
  | _, _, _, .trap hok => .trap hok
  | _, _, _, .throwRefInits hok => .throwRefInits hok

theorem AdminsOk.extend_aux {s s' : Store H} (hS : StoreOk s) (he : Extend s s') :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → AdminsOk s' C as it
  | _, _, _, .nil => .nil
  | _, _, _, .single h => .single (AdminOk.extend_aux hS he h)
  | _, _, _, .seq h₁ hx h₂ =>
    .seq (AdminsOk.extend_aux hS he h₁) hx (AdminsOk.extend_aux hS he h₂)
  | _, _, _, .cons ha hx hs =>
    .cons (AdminOk.extend_aux hS he ha) hx (AdminsOk.extend_aux hS he hs)
  | _, _, _, .sub h hsub hok => .sub (AdminsOk.extend_aux hS he h) hsub hok
  | _, _, _, .frame h hok => .frame (AdminsOk.extend_aux hS he h) hok

end

/-! ## Source code and values -/

theorem AdminsOk.of_instrsOk_aux {s : Store H} :
    ∀ {C : Context} {is : List Instr} {it : InstrType}, InstrsOk C is it →
      AdminsOk s C (expression is) it
  | _, _, _, .nil => .nil
  | _, _, _, .instr h => .single (.plain h)
  | _, _, _, .seq h₁ hx h₂ => by
    simpa [expression] using
      AdminsOk.seq (AdminsOk.of_instrsOk_aux (s := s) h₁) hx (AdminsOk.of_instrsOk_aux h₂)
  | _, _, _, .cons hi hx hs => .cons (.plain hi) hx (AdminsOk.of_instrsOk_aux hs)
  | _, _, _, .sub h hs hok => .sub (AdminsOk.of_instrsOk_aux h) hs hok
  | _, _, _, .frame h hok => .frame (AdminsOk.of_instrsOk_aux h) hok

/-- Source code types the same as administrative code (`Instr_ok2/plain`, lifted). -/
theorem AdminsOk.of_instrsOk {s : Store H} {C : Context} {is : List Instr} {it : InstrType}
    (h : InstrsOk C is it) : AdminsOk s C (expression is) it :=
  AdminsOk.of_instrsOk_aux h

theorem AdminOk.toAdmin_ok {s : Store H} {C : Context} {v : Val} {t : CValType}
    (h : ValOk s v t) : AdminOk s C v.toAdmin (.plain [] [t]) := by
  cases h with
  | num v =>
    rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩
    · exact .plain (.numeric (.intConst t b))
    · exact .plain (.numeric (.floatConst t b))
  | vec b => exact .plain (.vector (.vecConst b))
  | ref h => exact .ref h

/-- Inversion for a value instruction. -/
theorem AdminOk.toAdmin_inv {s : Store H} {C : Context} {v : Val} {it : InstrType}
    (h : AdminOk s C v.toAdmin it) : it.params = [] ∧ ∃ t, ValOk s v t ∧ it.results = [t] := by
  rcases v with ⟨⟨t⟩ | ⟨t⟩, b⟩ | b | r
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals exact ⟨rfl, _, .num ⟨.int t, b⟩, rfl⟩
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals exact ⟨rfl, _, .num ⟨.float t, b⟩, rfl⟩
  · cases h with
    | plain h =>
      cases h <;> try (rename_i hh; cases hh)
      all_goals exact ⟨rfl, _, .vec b, rfl⟩
  · cases h with
    | ref h => exact ⟨rfl, _, .ref h, rfl⟩

/-! ## Structural lemmas for administrative sequences (used by every soundness unit) -/

/-- `Instrs_ok2/seq` for arbitrary prefixes. -/
theorem AdminsOk.append {s : Store H} {C : Context} {as₁ as₂ : List Admin}
    {t₁ t₂ t₃ : List CValType} {xs₁ xs₂ : List Nat}
    (h₁ : AdminsOk s C as₁ ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
    (h₂ : AdminsOk s (C.initLocals xs₁) as₂ ⟨t₂, xs₂, t₃⟩) :
    AdminsOk s C (as₁ ++ as₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩ :=
  .seq h₁ hx h₂

/-! ### Monotonicity in locals, parameter regularity, splitting -/

mutual

theorem AdminOk.mono {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (h : AdminOk s C a it) {L : List LocalType} {r : Option (List CValType)}
    (hL : LocalsLe C.locals L) (hr : C.return_ = none ∨ C.return_ = r) :
    AdminOk s { C with locals := L, return_ := r } a it :=
  match h with
  | .plain h => .plain (InstrOk.mono h hL hr)
  | .callRefType hok hex => .callRefType hok hex
  | .returnCallRefType hok hex hret hsub hit =>
    .returnCallRefType hok hex (ret_mono hr hret) hsub (hit.mono hL)
  | .ref h => .ref h
  | .label hn hc hb => .label hn (AdminsOk.mono hc hL hr) (AdminsOk.mono hb hL hr)
  | .frame hf hn hb hok => .frame hf hn hb hok
  | .handler hc hb => .handler (fun c hc' => (hc c hc').mono) (AdminsOk.mono hb hL hr)
  | .trap hok => .trap (hok.mono hL)
  | .throwRefInits hok => .throwRefInits (hok.mono hL)

theorem AdminsOk.mono {s : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as it) {L : List LocalType} {r : Option (List CValType)}
    (hL : LocalsLe C.locals L) (hr : C.return_ = none ∨ C.return_ = r) :
    AdminsOk s { C with locals := L, return_ := r } as it :=
  match h with
  | .nil => .nil
  | .single h => .single (AdminOk.mono h hL hr)
  | .seq (xs₁ := xs₁) h₁ hx h₂ =>
      .seq (AdminsOk.mono h₁ hL hr) (fun x hx' => hL.exists (hx x hx'))
        (by
          rw [Context.initLocals_relax]
          exact AdminsOk.mono h₂ (LocalsLe.initLocals (C' := { C with locals := L, return_ := r })
            hL xs₁) (by simpa using hr))
  | .cons (xs₁ := xs₁) ha hx hs =>
      .cons (AdminOk.mono ha hL hr) (fun x hx' => hL.exists (hx x hx'))
        (by
          rw [Context.initLocals_relax]
          exact AdminsOk.mono hs (LocalsLe.initLocals (C' := { C with locals := L, return_ := r })
            hL xs₁) (by simpa using hr))
  | .sub h hs hok => .sub (AdminsOk.mono h hL hr) (hs.mono hL) (hok.mono hL)
  | .frame h hok => .frame (AdminsOk.mono h hL hr) hok

end

theorem AdminsOk.relocal {s : Store H} {C C' : Context} {as : List Admin} {it : InstrType}
    (h : AdminsOk s C as it) (hL : LocalsLe C.locals C'.locals)
    (hC : C' = { C with locals := C'.locals }) : AdminsOk s C' as it := by
  have := AdminsOk.mono h hL (r := C.return_) (.inr rfl)
  rw [hC]; exact this

theorem AdminsOk.initLocals_relocal {s : Store H} {C : Context} {xs ys : List Nat}
    {as : List Admin} {it : InstrType} (h : AdminsOk s (C.initLocals xs) as it)
    (hL : LocalsLe (C.initLocals xs).locals (C.initLocals ys).locals) :
    AdminsOk s (C.initLocals ys) as it := by
  refine h.relocal hL ?_
  rw [C.initLocals_eq_with ys, C.initLocals_eq_with xs]

theorem AdminsOk.id {s : Store H} {C : Context} {ts : List CValType}
    (h : ResultOk C.toTypeCtx ts) : AdminsOk s C [] ⟨ts, [], ts⟩ := by
  simpa using (AdminsOk.frame (s := s) (C := C) (ts := ts) AdminsOk.nil h)

/-- Parameters of an administrative instruction are well-formed in a well-formed
context, and its initialised locals exist. (Results need not be: `Ref_ok/struct`
types a reference by the instance's unconstrained `TYPE`.) -/
theorem AdminOk.params_ok {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (hC : C.Wf) (h : AdminOk s C a it) :
    ResultOk C.toTypeCtx it.params ∧ ∀ x ∈ it.inits, ∃ lt, C.locals[x]? = some lt := by
  cases h with
  | plain h => have r := h.regular hC; exact ⟨r.1, r.2.2⟩
  | callRefType hok hex =>
    have hok := wireCallRef_tyOk_of_empty C.toTypeCtx hok
    have := Expand.func_ok hok hex
    refine ⟨ResultOk.append this.1 ?_, by simp⟩
    simp [hok]
  | returnCallRefType hok hex _ _ hit =>
    have hok := wireCallRef_tyOk_of_empty C.toTypeCtx hok
    have := Expand.func_ok hok hex
    refine ⟨ResultOk.append (ResultOk.append hit.1 this.1) ?_, by simp⟩
    simp [hok]
  | ref _ => exact ⟨by simp, by simp⟩
  | label _ _ _ => exact ⟨by simp, by simp⟩
  | frame _ _ _ _ => exact ⟨by simp, by simp⟩
  | handler _ _ => exact ⟨by simp, by simp⟩
  | trap hok => exact ⟨hok.1, hok.2.2⟩
  | throwRefInits hok => exact ⟨hok.1, hok.2.2⟩

theorem AdminsOk.params_ok {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, C.Wf → AdminsOk s C as it →
      ResultOk C.toTypeCtx it.params ∧ ∀ x ∈ it.inits, ∃ lt, C.locals[x]? = some lt
  | _, _, _, _, .nil => ⟨by simp, by simp⟩
  | _, _, _, hC, .single h => h.params_ok hC
  | _, _, _, hC, .seq h₁ hx h₂ => by
    have r₁ := AdminsOk.params_ok hC h₁
    have r₂ := AdminsOk.params_ok (hC.initLocals _) h₂
    refine ⟨r₁.1, fun x hx' => ?_⟩
    rcases List.mem_append.mp hx' with h | h
    · exact hx x h
    · exact Context.initLocals_exists.mp (r₂.2 x h)
  | _, _, _, hC, .cons ha hx hs => by
    have r₁ := ha.params_ok hC
    have r₂ := AdminsOk.params_ok (hC.initLocals _) hs
    refine ⟨r₁.1, fun x hx' => ?_⟩
    rcases List.mem_append.mp hx' with h | h
    · exact hx x h
    · exact Context.initLocals_exists.mp (r₂.2 x h)
  | _, _, _, _, .sub _ _ hok => ⟨hok.1, hok.2.2⟩
  | _, _, _, hC, .frame h hok => by
    have r := AdminsOk.params_ok hC h
    exact ⟨ResultOk.append hok r.1, r.2⟩

/-- Splitting with a nonempty right part (no regularity of results needed), also
tracking how the locals initialised by the parts relate to those of the whole. -/
theorem AdminsOk.split {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → C.Wf →
      ∀ as₁ as₂, as = as₁ ++ as₂ → as₂ ≠ [] →
      ∃ t₂ xs₁ xs₂, AdminsOk s C as₁ ⟨it.params, xs₁, t₂⟩ ∧
        AdminsOk s (C.initLocals xs₁) as₂ ⟨t₂, xs₂, it.results⟩ ∧
        LocalsLe (C.initLocals it.inits).locals (C.initLocals (xs₁ ++ xs₂)).locals
  | _, _, _, .nil, _, as₁, as₂, e, hne => by
    obtain ⟨_, rfl⟩ := List.append_eq_nil_iff.mp e.symm
    exact absurd rfl hne
  | C, _, it₀, .single ha, hC, as₁, as₂, e, hne => by
    have r := ha.params_ok hC
    rcases List.append_eq_singleton_iff.mp e.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨it₀.params, [], it₀.inits, AdminsOk.id r.1, ?_, by simpa using LocalsLe.refl _⟩
      simpa using (AdminsOk.single ha : AdminsOk s C [_] it₀)
    · exact absurd rfl hne
  | C, _, _, .cons (t₁ := t₁) (xs₁ := xs₁') (xs₂ := xs₂') ha hx hs, hC, as₁, as₂, e, hne => by
    have ih := fun a₁ a₂ e' hne' => AdminsOk.split hs (hC.initLocals _) a₁ a₂ e' hne'
    rcases List.cons_eq_append_iff.mp e with ⟨rfl, rfl⟩ | ⟨a, rfl, rfl⟩
    · have hh : AdminsOk s C (_ :: _) ⟨t₁, xs₁' ++ xs₂', _⟩ := .cons ha hx hs
      exact ⟨t₁, [], xs₁' ++ xs₂', AdminsOk.id (ha.params_ok hC).1, hh,
        by simpa using LocalsLe.refl _⟩
    · obtain ⟨m, ya, yb, ha', hb, hL⟩ := ih a as₂ rfl hne
      refine ⟨m, xs₁' ++ ya, yb, .cons ha hx ha', ?_, ?_⟩
      · rw [Context.initLocals_append]; exact hb
      · simpa [Context.initLocals_append] using hL
  | C, _, _, .seq (as₂ := l₂) (t₂ := t₂') (t₃ := t₃') (xs₁ := xs₁') (xs₂ := xs₂') h₁ hx h₂, hC,
      as₁, as₂, e, hne => by
    have ih₁ := fun a₁ a₂ e' hne' => AdminsOk.split h₁ hC a₁ a₂ e' hne'
    have ih₂ := fun a₁ a₂ e' hne' => AdminsOk.split h₂ (hC.initLocals _) a₁ a₂ e' hne'
    rcases List.append_eq_append_iff.mp e with ⟨a, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
    · obtain ⟨m, ya, yb, ha, hb, hL⟩ := ih₂ a as₂ rfl hne
      refine ⟨m, xs₁' ++ ya, yb, .seq h₁ hx ha, ?_, ?_⟩
      · rw [Context.initLocals_append]; exact hb
      · simpa [Context.initLocals_append] using hL
    · by_cases hc : c = []
      · subst hc
        rw [List.append_nil] at h₁
        exact ⟨t₂', xs₁', xs₂', h₁, h₂, LocalsLe.refl _⟩
      obtain ⟨m, ya, yb, ha, hc', hL⟩ := ih₁ as₁ c rfl hc
      have hcx : ∀ x ∈ yb, ∃ lt, (C.initLocals ya).locals[x]? = some lt :=
        (AdminsOk.params_ok (hC.initLocals _) hc').2
      have h₂' : AdminsOk s ((C.initLocals ya).initLocals yb) l₂ ⟨t₂', xs₂', t₃'⟩ := by
        rw [← Context.initLocals_append]; exact h₂.initLocals_relocal hL
      refine ⟨m, ya, yb ++ xs₂', ha, .seq hc' hcx h₂', ?_⟩
      have := LocalsLe.initLocals (C := C.initLocals xs₁') (C' := C.initLocals (ya ++ yb))
        hL xs₂'
      simpa [← Context.initLocals_append] using this
  | C, _, _, .sub h hs hok, hC, as₁, as₂, e, hne => by
    obtain ⟨m, ya, yb, ha, hb, hL⟩ := AdminsOk.split h hC as₁ as₂ e hne
    have ra := AdminsOk.params_ok hC ha
    have rb := AdminsOk.params_ok (hC.initLocals _) hb
    have rm : ResultOk C.toTypeCtx m := by simpa using rb.1
    refine ⟨m, ya, yb, .sub ha ⟨hs.1, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩
        ⟨hok.1, rm, ra.2⟩,
      .sub hb ⟨ResultSub.refl _ _, by simpa using hs.2.1, fun _ h hn => absurd h hn⟩
        ⟨rb.1, by simpa using hok.2.1, rb.2⟩, ?_⟩
    exact LocalsLe.trans (LocalsLe.initLocals_of_sub hs.2.2) hL
  | _, _, _, .frame (ts := ts) h hok, hC, as₁, as₂, e, hne => by
    obtain ⟨m, ya, yb, ha, hb, hL⟩ := AdminsOk.split h hC as₁ as₂ e hne
    exact ⟨ts ++ m, ya, yb, .frame ha hok, .frame hb (by simpa using hok), hL⟩

/-- Splitting a typed administrative sequence. (Statement change: needs a
well-formed context, as `InstrsOk.append_inv`, and — when the right part is
empty — well-formed results: `[ref r]` may be typed by the unconstrained
`TYPE` of a struct instance, but the empty sequence only has well-formed types.) -/
theorem AdminsOk.append_inv {s : Store H} {C : Context} {as₁ as₂ : List Admin} {it : InstrType}
    (hC : C.Wf) (hr : as₂ ≠ [] ∨ ResultOk C.toTypeCtx it.results)
    (h : AdminsOk s C (as₁ ++ as₂) it) :
    ∃ t₂ xs₁ xs₂, AdminsOk s C as₁ ⟨it.params, xs₁, t₂⟩ ∧
      (∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt) ∧
      AdminsOk s (C.initLocals xs₁) as₂ ⟨t₂, xs₂, it.results⟩ := by
  by_cases hne : as₂ = []
  · subst hne
    have hr' : ResultOk C.toTypeCtx it.results := hr.resolve_left (fun h => h rfl)
    simp only [List.append_nil] at h
    refine ⟨it.results, it.inits, [], h, (AdminsOk.params_ok hC h).2, ?_⟩
    exact AdminsOk.id (by simpa using hr')
  · obtain ⟨t₂, xs₁, xs₂, h₁, h₂, -⟩ := AdminsOk.split h hC as₁ as₂ rfl hne
    exact ⟨t₂, xs₁, xs₂, h₁, (AdminsOk.params_ok hC h₁).2, h₂⟩

/-! ### Subtyping chains with a well-formed middle -/

/-- Equal, or a subtype of a well-formed type. -/
def SubEqR (Δ : TypeCtx) (a b : CValType) : Prop := a = b ∨ (Sub Δ a b ∧ TyOk Δ b)

/-- Equal, or a well-formed subtype. -/
def SubEqL (Δ : TypeCtx) (a b : CValType) : Prop := a = b ∨ (Sub Δ a b ∧ TyOk Δ a)

theorem SubEqR.sub {Δ : TypeCtx} {a b : CValType} (h : SubEqR Δ a b) : Sub Δ a b := by
  rcases h with rfl | ⟨h, _⟩
  · exact Sub.refl Δ (k := .val) trivial a
  · exact h

theorem SubEqL.sub {Δ : TypeCtx} {a b : CValType} (h : SubEqL Δ a b) : Sub Δ a b := by
  rcases h with rfl | ⟨h, _⟩
  · exact Sub.refl Δ (k := .val) trivial a
  · exact h

theorem SubEqR.trans {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : SubEqR Δ b c) : SubEqR Δ a c := by
  rcases h₁ with rfl | ⟨h₁, hb⟩
  · exact h₂
  rcases h₂ with rfl | ⟨h₂, hc⟩
  · exact .inr ⟨h₁, hb⟩
  exact .inr ⟨Sub.trans hΔ hb h₁ h₂, hc⟩

theorem SubEqR.sub_right {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : CValType} (h₁ : SubEqR Δ a b)
    (h₂ : Sub Δ b c) (hc : TyOk Δ c) : SubEqR Δ a c :=
  h₁.trans hΔ (.inr ⟨h₂, hc⟩)

theorem SubEqL.sub_left {Δ : TypeCtx} (hΔ : Δ.Ok) {a b c : CValType} (h₁ : Sub Δ a b)
    (ha : TyOk Δ a) (h₂ : SubEqL Δ b c) : SubEqL Δ a c := by
  rcases h₂ with rfl | ⟨h₂, hb⟩
  · exact .inr ⟨h₁, ha⟩
  exact .inr ⟨Sub.trans hΔ hb h₁ h₂, ha⟩

theorem forall₂_comp {α : Type} {P Q S : α → α → Prop} :
    ∀ {l₁ l₂ l₃ : List α}, List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₂ l₃ →
      (∀ a b c, a ∈ l₁ → b ∈ l₂ → c ∈ l₃ → P a b → Q b c → S a c) → List.Forall₂ S l₁ l₃
  | _, _, _, .nil, .nil, _ => .nil
  | a :: _, b :: _, c :: _, .cons h₁ t₁, .cons h₂ t₂, h =>
    .cons (h a b c (by simp) (by simp) (by simp) h₁ h₂)
      (forall₂_comp t₁ t₂ fun a b c ha hb hc =>
        h a b c (by simp [ha]) (by simp [hb]) (by simp [hc]))

theorem forall₂_self {α : Type} {R : α → α → Prop} (hR : ∀ a, R a a) :
    ∀ l : List α, List.Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (hR a) (forall₂_self hR l)

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₃ : List α} {l₂ l₄ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ →
      List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (forall₂_append t h')

theorem forall₂_subEqR_of_sub {Δ : TypeCtx} {l₁ l₂ : List CValType}
    (h : List.Forall₂ (Sub Δ) l₁ l₂) (hok : ResultOk Δ l₂) :
    List.Forall₂ (SubEqR Δ) l₁ l₂ :=
  forall₂_comp h (forall₂_self (R := Eq) (fun _ => rfl) l₂)
    fun _ _ c _ _ hc hab (e : _ = c) => by subst e; exact .inr ⟨hab, hok _ hc⟩

theorem forall₂_sub_trans {Δ : TypeCtx} (hΔ : Δ.Ok) {l₁ l₂ l₃ : List CValType}
    (h₁ : List.Forall₂ (Sub Δ) l₁ l₂) (h₂ : List.Forall₂ (Sub Δ) l₂ l₃) (hm : ResultOk Δ l₂) :
    List.Forall₂ (Sub Δ) l₁ l₃ :=
  forall₂_comp h₁ h₂ fun _ b _ _ hb _ hab hbc => Sub.trans hΔ (hm b hb) hab hbc

/-! ### Typings of the empty sequence -/

theorem AdminsOk.nil_aux {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → as = [] →
      C.toTypeCtx.Ok →
      ResultOk C.toTypeCtx it.params ∧ ResultOk C.toTypeCtx it.results ∧
        List.Forall₂ (Sub C.toTypeCtx) it.params it.results ∧
        ∀ x ∈ it.inits, ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _, _ => ⟨by simp [ResultOk], by simp [ResultOk], .nil, by simp⟩
  | _, _, _, .single _, e, _ => by cases e
  | _, _, _, .cons _ _ _, e, _ => by cases e
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, e, hΔ => by
    obtain ⟨e₁, e₂⟩ := List.append_eq_nil_iff.mp e
    obtain ⟨p₁, r₁, s₁, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ e₂ hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂ s₂
    refine ⟨p₁, r₂, forall₂_sub_trans hΔ s₁ s₂ r₁, ?_⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact i₁ x hx
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact i₁ x hx'
      · exact ⟨t, h'⟩
  | _, _, it', .sub (it := it) h hs hok, e, hΔ => by
    obtain ⟨p, r, sr, i⟩ := AdminsOk.nil_aux h e hΔ
    refine ⟨hok.1, hok.2.1, forall₂_sub_trans hΔ (forall₂_sub_trans hΔ hs.1 sr p) hs.2.1 r, ?_⟩
    intro x hx
    by_cases hx' : x ∈ it.inits
    · exact i x hx'
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame h hok, e, hΔ => by
    obtain ⟨p, r, sr, i⟩ := AdminsOk.nil_aux h e hΔ
    exact ⟨ResultOk.append hok p, ResultOk.append hok r,
      forall₂_append (forall₂_self (fun a => Sub.refl _ (k := .val) trivial a) _) sr, i⟩

/-! ### Single instructions -/

theorem AdminsOk.single_aux {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ a, as = [a] →
      C.toTypeCtx.Ok →
      ∃ ts it₀, AdminOk s C a it₀ ∧
        List.Forall₂ (SubEqL C.toTypeCtx) it.params (ts ++ it₀.params) ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (ts ++ it₀.results) it.results ∧
        ∀ x ∈ it.inits, x ∉ it₀.inits → ∃ t, C.locals[x]? = some ⟨.set, t⟩
  | _, _, _, .nil, _, e, _ => by cases e
  | _, _, it, .single h, a, e, _ => by
    cases e
    exact ⟨[], it, h, forall₂_self (fun _ => .inl rfl) _, forall₂_self (fun _ => .inl rfl) _,
      fun _ hx hn => absurd hx hn⟩
  | C, _, _, .cons (t₁ := t₁) (t₂ := t₂) (xs₁ := xs₁) ha _ hs, a, e, hΔ => by
    obtain ⟨rfl, e₂⟩ := List.cons_eq_cons.mp e
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux hs e₂ hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂ s₂
    refine ⟨[], ⟨t₁, xs₁, t₂⟩, ha, forall₂_self (fun _ => .inl rfl) _,
      forall₂_subEqR_of_sub s₂ r₂, ?_⟩
    intro x hx hn
    rcases List.mem_append.mp hx with hx | hx
    · exact absurd hx hn
    · obtain ⟨t, ht⟩ := i₂ x hx
      rcases Context.initLocals_set ht with hx' | h'
      · exact absurd hx' hn
      · exact ⟨t, h'⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, a, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    rcases List.append_eq_singleton_iff.mp e with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · obtain ⟨p₁, _, s₁, i₁⟩ := AdminsOk.nil_aux h₁ e₁ hΔ
      have hC : C.initLocals xs₁ = C := Context.initLocals_of_set i₁
      obtain ⟨ts, it₀, ha, hp, hr, hi⟩ := AdminsOk.single_aux h₂ a e₂ hΔ'
      rw [hC] at ha hp hr hi
      refine ⟨ts, it₀, ha, forall₂_comp s₁ hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (p₁ a ha') hbc, hr, ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact i₁ x hx
      · exact hi x hx hn
    · obtain ⟨ts, it₀, ha, hp, hr, hi⟩ := AdminsOk.single_aux h₁ a e₁ hΔ
      obtain ⟨_, r₂, s₂, i₂⟩ := AdminsOk.nil_aux h₂ e₂ hΔ'
      rw [Context.initLocals_toTypeCtx] at r₂ s₂
      refine ⟨ts, it₀, ha, hp, forall₂_comp hr s₂ fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (r₂ c hc), ?_⟩
      intro x hx hn
      rcases List.mem_append.mp hx with hx | hx
      · exact hi x hx hn
      · obtain ⟨t, ht⟩ := i₂ x hx
        rcases Context.initLocals_set ht with hx' | h'
        · exact hi x hx' hn
        · exact ⟨t, h'⟩
  | _, _, _, .sub (it := it) h hs hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hp, hr, hi⟩ := AdminsOk.single_aux h a e hΔ
    refine ⟨ts, it₀, ha, forall₂_comp hs.1 hp fun a _ _ ha' _ _ hab hbc =>
        SubEqL.sub_left hΔ hab (hok.1 a ha') hbc,
      forall₂_comp hr hs.2.1 fun _ _ c _ _ hc hab hbc =>
        SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc), ?_⟩
    intro x hx hn
    by_cases hx' : x ∈ it.inits
    · exact hi x hx' hn
    · exact hs.2.2 x hx hx'
  | _, _, _, .frame (ts := F) h hok, a, e, hΔ => by
    obtain ⟨ts, it₀, ha, hp, hr, hi⟩ := AdminsOk.single_aux h a e hΔ
    refine ⟨F ++ ts, it₀, ha, ?_, ?_, hi⟩
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hp
    · rw [List.append_assoc]
      exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) hr

/-- Principal inversion for a single administrative instruction. (Statement
change: needs `C.toTypeCtx.Ok` to compose subsumptions, cf. `InstrsOk.single_inv`,
which needs `C.Wf`.) -/
theorem AdminsOk.single_inv {s : Store H} {C : Context} {a : Admin} {it : InstrType}
    (hΔ : C.toTypeCtx.Ok) (h : AdminsOk s C [a] it) :
    ∃ ts it₀, AdminOk s C a it₀ ∧
      InstrTypeSub C ⟨ts ++ it₀.params, it₀.inits, ts ++ it₀.results⟩ it := by
  obtain ⟨ts, it₀, ha, hp, hr, hi⟩ := AdminsOk.single_aux h a rfl hΔ
  exact ⟨ts, it₀, ha, hp.imp fun _ _ h => h.sub, hr.imp fun _ _ h => h.sub, hi⟩

/-- Values push their types. (Statement change: the pushed types must be
well-formed, since every typed sequence has well-formed intermediate stacks
below a later push, e.g. `[v₁, v₂]` needs `Instrs_ok/frame` over `t₁`.) -/
theorem AdminsOk.of_vals {s : Store H} {C : Context} {vs : List Val} {ts : List CValType}
    (h : List.Forall₂ (ValOk s) vs ts) (hok : ResultOk C.toTypeCtx ts) :
    AdminsOk s C (vals vs) (.plain [] ts) := by
  induction h with
  | nil => exact .nil
  | @cons v t vs ts hv _ ih =>
    have h2 : AdminsOk s C (vals vs) ⟨[t] ++ [], [], [t] ++ ts⟩ :=
      .frame (ih fun x hx => hok x (by simp [hx])) (fun x hx => hok x (by simp_all))
    exact AdminsOk.cons (xs₁ := []) (AdminOk.toAdmin_ok hv) (by simp) h2

theorem AdminsOk.vals_aux {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → ∀ vs, as = vals vs →
      C.toTypeCtx.Ok →
      ResultOk C.toTypeCtx it.params ∧ ∃ ts, List.Forall₂ (ValOk s) vs ts ∧
        List.Forall₂ (SubEqR C.toTypeCtx) (it.params ++ ts) it.results
  | _, _, _, .nil, vs, e, _ => by
    have : vs = [] := List.map_eq_nil_iff.mp e.symm
    subst this
    exact ⟨by simp [ResultOk], [], .nil, .nil⟩
  | _, _, _, .single h, vs, e, _ => by
    obtain ⟨v, rfl, hv⟩ := List.map_eq_singleton_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv h
    refine ⟨by simp [hp, ResultOk], [t], .cons hv .nil, ?_⟩
    rw [hp, hr]
    exact forall₂_self (fun _ => .inl rfl) _
  | C, _, _, .cons (xs₁ := xs₁) ha _ hs, vs, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨v, vs', rfl, hv, e'⟩ := List.map_eq_cons_iff.mp e.symm
    subst hv
    obtain ⟨hp, t, hv, hr⟩ := AdminOk.toAdmin_inv ha
    obtain ⟨_, ts', hv', r⟩ := AdminsOk.vals_aux hs vs' e'.symm hΔ'
    simp only at hp hr
    subst hp hr
    rw [Context.initLocals_toTypeCtx] at r
    exact ⟨by simp [ResultOk], t :: ts', .cons hv hv', r⟩
  | C, _, _, .seq (xs₁ := xs₁) h₁ _ h₂, vs, e, hΔ => by
    have hΔ' : (C.initLocals xs₁).toTypeCtx.Ok := by rw [Context.initLocals_toTypeCtx]; exact hΔ
    obtain ⟨vs₁, vs₂, rfl, e₁, e₂⟩ := List.map_eq_append_iff.mp e.symm
    obtain ⟨p₁, ts₁, v₁, r₁⟩ := AdminsOk.vals_aux h₁ vs₁ e₁.symm hΔ
    obtain ⟨_, ts₂, v₂, r₂⟩ := AdminsOk.vals_aux h₂ vs₂ e₂.symm hΔ'
    rw [Context.initLocals_toTypeCtx] at r₂
    refine ⟨p₁, ts₁ ++ ts₂, forall₂_append v₁ v₂, ?_⟩
    rw [← List.append_assoc]
    exact forall₂_comp (forall₂_append r₁ (forall₂_self (fun _ => .inl rfl) ts₂)) r₂
      fun _ _ _ _ _ _ hab hbc => hab.trans hΔ hbc
  | _, _, _, .sub h hs hok, vs, e, hΔ => by
    obtain ⟨p, ts, hv, r⟩ := AdminsOk.vals_aux h vs e hΔ
    refine ⟨hok.1, ts, hv, ?_⟩
    have h1 : List.Forall₂ (SubEqR _) _ _ :=
      forall₂_append (forall₂_subEqR_of_sub hs.1 p) (forall₂_self (fun _ => .inl rfl) ts)
    exact forall₂_comp (forall₂_comp h1 r fun _ _ _ _ _ _ hab hbc => hab.trans hΔ hbc) hs.2.1
      fun _ _ c _ _ hc hab hbc => SubEqR.sub_right hΔ hab hbc (hok.2.1 c hc)
  | _, _, _, .frame (ts := F) h hok, vs, e, hΔ => by
    obtain ⟨p, ts, hv, r⟩ := AdminsOk.vals_aux h vs e hΔ
    refine ⟨ResultOk.append hok p, ts, hv, ?_⟩
    rw [List.append_assoc]
    exact forall₂_append (forall₂_self (fun _ => .inl rfl) _) r

/-- Inversion for a value sequence: it pushes (subtypes of) its value types.
(Statement change: needs `C.toTypeCtx.Ok` to compose subsumptions.) -/
theorem AdminsOk.vals_inv {s : Store H} {C : Context} {vs : List Val} {t₁ t₂ : List CValType}
    {xs : List Nat} (hΔ : C.toTypeCtx.Ok) (h : AdminsOk s C (vals vs) ⟨t₁, xs, t₂⟩) :
    ∃ ts, List.Forall₂ (ValOk s) vs ts ∧ ResultSub C.toTypeCtx (t₁ ++ ts) t₂ := by
  obtain ⟨_, ts, hv, r⟩ := AdminsOk.vals_aux h vs rfl hΔ
  exact ⟨ts, hv, r.imp fun _ _ h => h.sub⟩

/-- Typing of administrative code is preserved by store extension. (Statement
change: needs `StoreOk s`, as `Frame_ok` contains `Moduleinst_ok`, whose memory
and table types are only recovered after growth by subsumption, which needs them
valid.) -/
theorem AdminsOk.extend {s s' : Store H} {C : Context} {as : List Admin} {it : InstrType}
    (hs : StoreOk s) (he : Extend s s') (h : AdminsOk s C as it) : AdminsOk s' C as it :=
  AdminsOk.extend_aux hs he h

/-! ### The `throw_ref`/`trap` inits deviation: inversion helpers -/

theorem ResultOk.append' {Δ : TypeCtx} {a b : List CValType} (ha : ResultOk Δ a)
    (hb : ResultOk Δ b) : ResultOk Δ (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem ResultOk.exnref (Δ : TypeCtx) : ResultOk Δ [.refT true (.abs .exn)] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  exact .refv (.ref (.abs .exn))

/-- `throw_ref` has typings of different arities, so it cannot satisfy a fixed-arity
hypothesis. -/
theorem InstrOk.throwRef_arity_absurd {C : Context} {n : Nat}
    (h : ∀ it', InstrOk C .throwRef it' → it'.params.length = n) : False := by
  have h1 := h _ (InstrOk.throwRef (t₁ := []) (t₂ := [])
    ⟨by simp [ResultOk], by simp [ResultOk], by simp⟩)
  have h2 := h _ (InstrOk.throwRef (t₁ := [.refT true (.abs .exn)]) (t₂ := [])
    ⟨ResultOk.exnref _, by simp [ResultOk], by simp⟩)
  simp at h1 h2
  omega

/-- Inversion of `AdminOk` at a plain instruction (with the `throwRefInits` deviation). -/
theorem AdminOk.plain_cases {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    (h : AdminOk s C (.plain i) it) :
    InstrOk C i it ∨ (i = .throwRef ∧ ∃ t₁ t₂ xs, it = ⟨t₁ ++ [.refT true (.abs .exn)], xs, t₂⟩ ∧
      InstrTypeOk C it) := by
  cases h with
  | plain h => exact .inl h
  | throwRefInits hok => exact .inr ⟨rfl, _, _, _, rfl, hok⟩

/-- Inversion of `AdminOk` at a plain instruction other than `throw_ref`. -/
theorem AdminOk.plain_inv_ne {s : Store H} {C : Context} {i : Instr} {it : InstrType}
    (h : AdminOk s C (.plain i) it) (hne : i ≠ .throwRef := by intro h; cases h) :
    InstrOk C i it := by
  rcases h.plain_cases with h | ⟨rfl, _⟩
  · exact h
  · exact absurd rfl hne

/-- Inversion of `AdminOk` at a plain instruction whose typings have a fixed arity. -/
theorem AdminOk.plain_inv_arity {s : Store H} {C : Context} {i : Instr} {it : InstrType} {n : Nat}
    (h : AdminOk s C (.plain i) it) (hI : ∀ it', InstrOk C i it' → it'.params.length = n) :
    InstrOk C i it := by
  rcases h.plain_cases with h | ⟨rfl, _⟩
  · exact h
  · exact (InstrOk.throwRef_arity_absurd hI).elim

/-- `trap` is typed at every valid instruction type (deviation, see the module doc). -/
theorem AdminsOk.trap_it {s : Store H} {C : Context} {it : InstrType}
    (hok : InstrTypeOk C it) : AdminsOk s C [.trap] it := by
  obtain ⟨t₁, xs, t₂⟩ := it
  exact .single (.trap hok)

/-- `REF.EXN_ADDR a; THROW_REF` (for an existing exception address) is typed at every
valid instruction type (deviation, see the module doc). -/
theorem AdminsOk.throwing_it {s : Store H} {C : Context} {a : Nat} {it : InstrType}
    (he : ∃ e, s.exns[a]? = some e) (hok : InstrTypeOk C it) :
    AdminsOk s C [.ref (.exn a), .plain .throwRef] it := by
  obtain ⟨e, he⟩ := he
  obtain ⟨t₁, xs, t₂⟩ := it
  have hr : RefOk s (.exn a) (.ref true (.abs .exn)) :=
    .sub (.exn he) (.ref (.abs .exn)) (.refNull .heapRefl)
  have h₁ : AdminsOk s C [.ref (.exn a)] ⟨t₁, [], t₁ ++ [.refv (.ref true (.abs .exn))]⟩ := by
    simpa using AdminsOk.frame (ts := t₁) (AdminsOk.single (AdminOk.ref (C := C) hr)) hok.1
  have h₂ : AdminsOk s (C.initLocals []) [.plain .throwRef]
      ⟨t₁ ++ [.refT true (.abs .exn)], xs, t₂⟩ :=
    .single (.throwRefInits ⟨ResultOk.append' hok.1 (ResultOk.exnref _), hok.2.1, hok.2.2⟩)
  simpa using AdminsOk.seq h₁ (by simp) h₂

/-- Results of code made of plain instructions are valid. -/
theorem AdminsOk.results_of_plain {s : Store H} :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → C.Wf →
      (∀ a ∈ as, ∃ i, a = .plain i) → ResultOk C.toTypeCtx it.results
  | _, _, _, .nil, _, _ => by simp [ResultOk]
  | _, _, _, .single h, hC, hp => by
    obtain ⟨i, rfl⟩ := hp _ (List.mem_singleton_self _)
    cases h with
    | plain h => exact (h.regular hC).2.1
    | throwRefInits hok => exact hok.2.1
  | _, _, _, .seq h₁ _ h₂, hC, hp => by
    have := AdminsOk.results_of_plain h₂ (hC.initLocals _)
      (fun a ha => hp a (List.mem_append_right _ ha))
    rw [Context.initLocals_toTypeCtx] at this
    exact this
  | _, _, _, .cons _ _ hs, hC, hp => by
    have := AdminsOk.results_of_plain hs (hC.initLocals _)
      (fun a ha => hp a (List.mem_cons_of_mem _ ha))
    rw [Context.initLocals_toTypeCtx] at this
    exact this
  | _, _, _, .sub _ _ hok, _, _ => hok.2.1
  | _, _, _, .frame h hok, hC, hp => ResultOk.append' hok (AdminsOk.results_of_plain h hC hp)

/-- Code made of plain instructions has a valid instruction type. -/
theorem AdminsOk.instrTypeOk_of_plain {s : Store H} {C : Context} {as : List Admin}
    {it : InstrType} (hC : C.Wf) (h : AdminsOk s C as it) (hp : ∀ a ∈ as, ∃ i, a = .plain i) :
    InstrTypeOk C it :=
  ⟨(h.params_ok hC).1, h.results_of_plain hC hp, (h.params_ok hC).2⟩

end Silmaril.Wasm.Execution.Core
