module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.WholeFwdPR

/-!
# The remaining scalar pure rules forward

Pass 1 of round 3 assembled fifteen `PureStep` rules (`PureFrag20`). This module adds the
remaining scalar ones, each with V2's premises, as a second base fragment for `fwd_nest20`:
`select`, `if`, `br_if`, `br_table`, `br` (zero and succ), `return` (frame and label),
`trap-vals`, `local.tee`, `ref.is_null`, `cvtop` (value and trap) and the three trap rules that
V2 states but never fires (`unop-trap` integer and float, float `binop-trap`).

* **`instr` and `admininstr` agree on instructions** (`typedV_admin_iff_instr20`): the case list
  of `admininstr` is the case list of `instr` followed by six administrative cases
  (`recCases_admininstr20`), and no V2 instruction is encoded with one of their heads
  (`instrToV_notAdmin20`). So a code sequence `expression is` is a typed `admininstr*` exactly when
  `is` is a typed `instr*` (`typedV_admins_expression20_iff`).
* **Inversions** of the typed instruction cases the rules need (`IF`, `BLOCK`, `SELECT`, `BR_IF`,
  `BR_TABLE`, `LOCAL.TEE`, `CVTOP`).
* **`PureFrag20B P`**: the new rules. `br`, `return` and `trap-vals` quantify the code after the
  redex as `instr*` in the 2.0 script, while V2 allows any administrative code there. The
  fragment keeps V2's premises and asks that code to be plain (`rest = expression is`), which
  is what happens in every configuration reached from plain code: V2 reduces the leftmost
  redex, so everything to its right is still plain.
* `spure_of_pureFrag20B`, `typedV_succ_pureFrag20B`, `fwdBase20_pureB`: each rule is a
  `Step_pure` derivation of the original script from a typed image at `NumAgree`/`CvtAgree`
  builtins, the successor image is typed, and the fragment at any state is a `FwdBase20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.SpecTec.Equiv.Execution (caseNilV pctV)
open Silmaril.Wasm.SpecTec.Sim (TypedV SPure)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase recCases)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Scripts.Wasm20 (Original.d295)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## `instr` and `admininstr` -/

/-- The six administrative cases of the 2.0 `admininstr`, after those of `instr`. -/
noncomputable def adminCases20 : List TypCase := (recCases Original.d295 0 0).drop instrCases20.length

/-- Their heads. -/
def adminHeads20 : List MixopS :=
  ["REF.FUNC_ADDR", "REF.HOST_ADDR", "CALL_ADDR", "LABEL_%{%}%", "FRAME_%{%}%", "TRAP"]

/-- **`admininstr`'s cases are `instr`'s, then the administrative ones.** -/
theorem recCases_admininstr20 : recCases Original.d295 0 0 = instrCases20 ++ adminCases20 := rfl

theorem adminCases20_heads : adminCases20.map caseHead = adminHeads20 := rfl

/-- A case found in a list of cases none of whose later cases has the head is found in the
prefix. -/
theorem hasTypCase_append_iff {env : Env} {ρ : VarEnv} {cs ds : List TypCase} {op : MixopS}
    {w : Value} (hd : op ∉ ds.map caseHead) :
    HasTypCase env ρ (cs ++ ds) op w ↔ HasTypCase env ρ cs op w := by
  induction cs with
  | nil =>
    refine ⟨fun h => ?_, fun h => absurd h not_hasTypCase_nil⟩
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem h
    exact absurd (List.mem_map_of_mem (f := caseHead) hm) hd
  | cons c cs ih =>
    obtain ⟨o, t, qs, prems⟩ := c
    by_cases ho : o = op
    · rw [List.cons_append, hasTypCase_cons_hit_iffQ ho, hasTypCase_cons_hit_iffQ ho]
    · rw [List.cons_append, hasTypCase_cons_miss_iff ho, hasTypCase_cons_miss_iff ho]
      exact ih

/-- **Every V2 instruction is encoded as a case whose head is not administrative.** -/
theorem instrToV_notAdmin20 (i : V2.Instr) : ∃ op w, instrToV i = .case op w ∧ op ∉ adminHeads20 := by
  cases i <;> simp [instrToV, caseNilV, adminHeads20, valV]

/-- The empty scope binds values only. -/
theorem valsOnly_empty20 : Sim.ValsOnly VarEnv.empty := ⟨rfl, rfl, rfl⟩

/-- **On a non-administrative head, `instr` and `admininstr` type the same values.** -/
theorem typedV_admin_iff_instr20 {op : MixopS} {w : Value} (hop : op ∉ adminHeads20) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (.case op w) ↔
      TypedV (simEnv20 B) (.varT "instr" []) (.case op w) := by
  have hd : op ∉ adminCases20.map caseHead := adminCases20_heads ▸ hop
  constructor
  · intro h
    obtain ⟨op', w', he, hc⟩ :=
      hasTypDef_variantT_iff.1 (hasTypDef_of_closed findTyp_admininstr20 (h _ valsOnly_empty20))
    obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
    rw [recCases_admininstr20, hasTypCase_append_iff hd] at hc
    exact typedV_of_empty20 (hasTyp_varT_case rfl (findTyp_instr20 B) Equiv.evalArgs_nil
      matchArgs_nil hc)
  · intro h
    obtain ⟨op', w', he, hc⟩ :=
      hasTypDef_variantT_iff.1 (hasTypDef_of_closed (findTyp_instr20 B) (h _ valsOnly_empty20))
    obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
    rw [← hasTypCase_append_iff hd, ← recCases_admininstr20] at hc
    exact typedV_of_empty20 (hasTyp_varT_case rfl findTyp_admininstr20 Equiv.evalArgs_nil
      matchArgs_nil hc)

/-- **A plain instruction is a typed `admininstr` exactly when it is a typed `instr`.** -/
theorem typedV_plain20_iff (i : V2.Instr) :
    TypedV (simEnv20 B) (.varT "admininstr" []) (instrToV i) ↔
      TypedV (simEnv20 B) (.varT "instr" []) (instrToV i) := by
  obtain ⟨op, w, he, hop⟩ := instrToV_notAdmin20 i
  rw [he]
  exact typedV_admin_iff_instr20 hop

/-- `instrsToV` is a map. -/
theorem instrsToV_map20 : ∀ is : List V2.Instr, instrsToV is = is.map instrToV
  | [] => rfl
  | i :: is => by rw [List.map_cons, ← instrsToV_map20 is]; rfl

/-- **Plain code is a typed `admininstr*` exactly when it is a typed `instr*`.** -/
theorem typedV_admins_expression20_iff (is : List V2.Instr) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV (expression is))) ↔
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV is)) := by
  rw [Pure.adminsToV_expression, Sim.typedV_list_iff, Sim.typedV_list_iff]
  constructor
  · intro h u hu
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (instrsToV_map20 is ▸ hu)
    exact (typedV_plain20_iff i).1 (h _ hu)
  · intro h u hu
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 (instrsToV_map20 is ▸ hu)
    exact (typedV_plain20_iff i).2 (h _ hu)

/-! ## Inversions and constructions of typed instruction cases -/

/-- A typed two-component tuple, taken apart. -/
theorem hasTyp_tup2_inv20 {env : Env} {a b : IL.Id} {τ₁ τ₂ : Typ} {u v : Value}
    (h : HasTyp env VarEnv.empty (.tupT [.mk a τ₁, .mk b τ₂]) (.tuple [u, v])) :
    HasTyp env VarEnv.empty τ₁ u ∧ HasTyp env (VarEnv.empty.bindVal a u) τ₂ v := by
  obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 h
  obtain rfl := (Value.tuple.inj hvs).symm
  obtain ⟨y₁, ys₁, h₁, hy₁, ht₁⟩ := hasTypTup_cons_iff.1 htup
  obtain ⟨rfl, rfl⟩ := List.cons.inj h₁
  obtain ⟨y₂, ys₂, h₂, hy₂, -⟩ := hasTypTup_cons_iff.1 ht₁
  obtain ⟨rfl, -⟩ := List.cons.inj h₂
  exact ⟨hy₁, hy₂⟩

/-- An option of lists over a closed type name, from the empty scope to every scope that binds
values only. -/
theorem typedV_optList_of_empty20 {env : Env} {x : IL.Id} {v : Value}
    (h : HasTyp env VarEnv.empty (.iterT (.iterT (.varT x []) .list) .opt) v) :
    TypedV env (.iterT (.iterT (.varT x []) .list) .opt) v := by
  intro ρ hρ
  rcases hasTyp_iterT_opt_iff.1 h with rfl | ⟨w, rfl, hw⟩
  · exact hasTyp_iterT_opt_iff.2 (.inl rfl)
  · obtain ⟨l, rfl, -⟩ := hasTyp_iterT_list_iff.1 hw
    exact hasTyp_iterT_opt_iff.2 (.inr ⟨_, rfl, typedV_list_of_empty20 hw ρ hρ⟩)

/-- A typed plain instruction, as an `admininstr`. -/
abbrev TypedI (B : Builtins) (i : V2.Instr) : Prop :=
  TypedV (simEnv20 B) (.varT "admininstr" []) (instrToV i)

theorem typed_if20 {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} (h : TypedI B (.if_ bt b₁ b₂)) :
    TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b₁)) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b₂)) := by
  obtain ⟨h₁, h₂, h₃⟩ := hasTyp_tup3_inv20 (hasTyp_adminCase20 rfl h)
  exact ⟨h₁, typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩

theorem typed_block20 {bt : V2.BlockType} {b : List V2.Instr}
    (h₁ : TypedV (simEnv20 B) Pure.blocktypeT (blockTypeV bt))
    (h₂ : TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV b))) : TypedI B (.block bt b) :=
  Pure.typedV_closedCase20 findTyp_admininstr20 rfl (hasTyp_tup2G h₁ h₂)

theorem typed_select20 {ts : Option (List V2.ValType)} (h : TypedI B (.select ts)) :
    TypedV (simEnv20 B) Pure.valtypesOptT (.opt ((Pure.selAnnot ts).map .list)) := by
  rw [TypedI, Pure.instrToV_select] at h
  exact typedV_optList_of_empty20 (hasTyp_adminCase20 rfl h)

theorem typed_brIf20 {l : LabelIdx} (h : TypedI B (.brIf l)) :
    TypedV (simEnv20 B) Pure.labelidxT (idxV l) :=
  typedV_of_empty20 (hasTyp_adminCase20 rfl h)

theorem typed_br20 {l : LabelIdx} (h : TypedV (simEnv20 B) Pure.labelidxT (idxV l)) :
    TypedI B (.br l) :=
  Pure.typedV_closedCase20 findTyp_admininstr20 rfl (h _ valsOnly_empty20)

theorem typed_brTable20 {ls : List LabelIdx} {l : LabelIdx} (h : TypedI B (.brTable ls l)) :
    TypedV (simEnv20 B) Pure.labelidxsT (.list (ls.map idxV)) ∧
      TypedV (simEnv20 B) Pure.labelidxT (idxV l) := by
  obtain ⟨h₁, h₂⟩ := hasTyp_tup2_inv20 (hasTyp_adminCase20 rfl h)
  exact ⟨typedV_list_of_empty20 h₁, typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂⟩

theorem typed_return20 : TypedI B .return_ :=
  Pure.typedV_closedCase20 findTyp_admininstr20 rfl hasTyp_tupT_nil

theorem typed_localSet_of_tee20 {x : LocalIdx} (h : TypedI B (.localTee x)) :
    TypedI B (.localSet x) :=
  Pure.typedV_closedCase20 findTyp_admininstr20 rfl (hasTyp_adminCase20 rfl h)

/-- Every label index is a `labelidx`. -/
theorem typedV_labelidx20 (l : LabelIdx) : TypedV (simEnv20 B) Pure.labelidxT (idxV l) :=
  typedV_aliasG Pure.findTyp_labelidx20 (typedV_idx20 l _ valsOnly_empty20)

/-! ## The second pure fragment -/

/-- **The remaining scalar `PureStep` rules**, with V2's premises. Where the 2.0 rule quantifies
the code after the redex as `instr*`, that code is plain (`expression is`). `cvtop` also carries
V2's `toShared` side condition, which every validated conversion meets. -/
inductive PureFrag20B (P : Profile) : List Admin → List Admin → Prop where
  | selectTrue {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List V2.ValType)} (hc : c ≠ 0) :
      PureFrag20B P [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)] [v₁.toAdmin]
  | selectFalse (v₁ v₂ : Val) (ts : Option (List V2.ValType)) :
      PureFrag20B P [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)] [v₂.toAdmin]
  | ifTrue {c : BitVec 32} {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} (hc : c ≠ 0) :
      PureFrag20B P [constI32 c, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₁)]
  | ifFalse {bt : V2.BlockType} {b₁ b₂ : List V2.Instr} :
      PureFrag20B P [constI32 0, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₂)]
  | brZero {n : Nat} {cont : List V2.Instr} {vs' vs : List Val} {l : LabelIdx}
      {is : List V2.Instr} (hl : l.toNat = 0) (hn : vs.length = n) :
      PureFrag20B P [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ expression is)]
        (vals vs ++ expression cont)
  | brSucc {n : Nat} {cont : List V2.Instr} {vs : List Val} {l : LabelIdx} {is : List V2.Instr}
      (hl : 0 < l.toNat) :
      PureFrag20B P [.label n cont (vals vs ++ [.plain (.br l)] ++ expression is)]
        (vals vs ++ [.plain (.br (labelPred l))])
  | brIfTrue {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0) :
      PureFrag20B P [constI32 c, .plain (.brIf l)] [.plain (.br l)]
  | brIfFalse {l : LabelIdx} : PureFrag20B P [constI32 0, .plain (.brIf l)] []
  | brTableLt {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (hi : ls[i.toNat]? = some l) :
      PureFrag20B P [constI32 i, .plain (.brTable ls l')] [.plain (.br l)]
  | brTableGe {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx} (hi : ls.length ≤ i.toNat) :
      PureFrag20B P [constI32 i, .plain (.brTable ls l')] [.plain (.br l')]
  | returnFrame {n : Nat} {fr : Frame} {vs' vs : List Val} {is : List V2.Instr}
      (hn : vs.length = n) :
      PureFrag20B P [.frame n fr (vals vs' ++ vals vs ++ [.plain .return_] ++ expression is)]
        (vals vs)
  | returnLabel {n : Nat} {cont : List V2.Instr} {vs : List Val} {is : List V2.Instr} :
      PureFrag20B P [.label n cont (vals vs ++ [.plain .return_] ++ expression is)]
        (vals vs ++ [.plain .return_])
  | trapVals {vs : List Val} {is : List V2.Instr} (hne : vs ≠ [] ∨ expression is ≠ []) :
      PureFrag20B P (vals vs ++ [.trap] ++ expression is) [.trap]
  | cvtOp {target source : NumType} {op : V2.CvtOp} {x : BitVec source.width}
      {z : BitVec target.width} (hop : (V2.CvtOp.toShared target source op).isSome)
      (h : CvtOpResult P target source op x z) :
      PureFrag20B P [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)]
        [(Val.num ⟨target, z⟩).toAdmin]
  | cvtOpTrap {target source : NumType} {op : V2.CvtOp} {x : BitVec source.width}
      (hop : (V2.CvtOp.toShared target source op).isSome) (h : CvtOpTraps P target source op x) :
      PureFrag20B P [(Val.num ⟨source, x⟩).toAdmin, .plain (.cvtOp target source op)] [.trap]
  | refIsNullTrue {t : V2.RefType} : PureFrag20B P [aref (.null t), .plain .refIsNull] [constI32 1]
  | refIsNullFalse {r : Ref} (h : ∀ t, r ≠ .null t) :
      PureFrag20B P [aref r, .plain .refIsNull] [constI32 0]
  | localTee {x : LocalIdx} {v : Val} :
      PureFrag20B P [v.toAdmin, .plain (.localTee x)] [v.toAdmin, v.toAdmin, .plain (.localSet x)]

/-- Every rule of the fragment is a V2 `PureStep`. -/
theorem PureFrag20B.pureStep {P : Profile} {is is' : List Admin} (h : PureFrag20B P is is') :
    PureStep P is is' := by
  cases h with
  | selectTrue hc => exact .selectTrue hc
  | selectFalse v₁ v₂ ts => exact .selectFalse v₁ v₂ ts
  | ifTrue hc => exact .ifTrue hc
  | ifFalse => exact .ifFalse
  | brZero hl hn => exact .brZero hl hn
  | brSucc hl => exact .brSucc hl
  | brIfTrue hc => exact .brIfTrue hc
  | brIfFalse => exact .brIfFalse
  | brTableLt hi => exact .brTableLt hi
  | brTableGe hi => exact .brTableGe hi
  | returnFrame hn => exact .returnFrame hn
  | returnLabel => exact .returnLabel
  | trapVals hne => exact .trapVals hne
  | cvtOp _ h => exact .cvtOp h
  | cvtOpTrap _ h => exact .cvtOpTrap h
  | refIsNullTrue => exact .refIsNullTrue
  | refIsNullFalse h => exact .refIsNullFalse h
  | localTee => exact .localTee

/-- A plain instruction of a typed code sequence is typed. -/
theorem typedI_of_mem {is : List Admin} {i : V2.Instr}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV is))) (hm : .plain i ∈ is) :
    TypedI B i :=
  Sim.typedV_list_iff.1 hc _ (Pure.adminsToV_eq_map is ▸ List.mem_map_of_mem (f := adminToV) hm)

/-- The plain tail of a typed code sequence is a typed `instr*`. -/
theorem typedV_tail20 {l : List Admin} {is : List V2.Instr}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV (l ++ expression is)))) :
    TypedV (simEnv20 B) Pure.instrsT (.list (adminsToV (expression is))) := by
  rw [Pure.adminsToV_expression]
  exact (typedV_admins_expression20_iff is).1 (typedV_admins_append20_iff.1 hc).2

/-- The parts of a typed label: arity, continuation and body. -/
theorem label_all20 {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV [.label n cont body]))) :
    TypedV (simEnv20 B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20 B) Pure.instrsT (.list (instrsToV cont)) ∧
      TypedV (simEnv20 B) adminsTy (.list (adminsToV body)) :=
  typedV_adminLabel20_iff.1 (typedV_admins_single20_iff.1 hc)

/-- The parts of a typed frame: arity, frame and body. -/
theorem frame_all20 {n : Nat} {fr : Frame} {body : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV [.frame n fr body]))) :
    TypedV (simEnv20 B) Pure.nT (.num (.natN n)) ∧
      TypedV (simEnv20 B) Pure.frameT (frameV fr) ∧
      TypedV (simEnv20 B) adminsTy (.list (adminsToV body)) :=
  typedV_adminFrame20_iff.1 (typedV_admins_single20_iff.1 hc)

/-- **Every rule of the second fragment, from a typed image, is a `Step_pure` derivation of the
original script**, at `NumAgree` and `CvtAgree` builtins. -/
theorem spure_of_pureFrag20B {P : Profile} (C : Pure.CvtAgree (simEnv20 B) P)
    {is is' : List Admin} (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV is)))
    (h : PureFrag20B P is is') : SPure (simEnv20 B) (adminsToV is) (adminsToV is') := by
  have T : Pure.NumTyped (simEnv20 B) := Pure.numTyped_simEnv20 B
  cases h with
  | @selectTrue v₁ v₂ c ts hc' =>
    have ht : TypedV (simEnv20 B) Pure.valtypesOptT (.opt ((Pure.selAnnot ts).map .list)) :=
      typed_select20 (typedI_of_mem (i := .select ts) hc (by simp))
    exact spure_of_firesB20 ((Pure.selectTrue_iff B
      ⟨typedV_val20 _, typedV_val20 _, T.i32 _, ht⟩).2 ⟨hc', rfl⟩)
  | selectFalse v₁ v₂ ts =>
    have ht : TypedV (simEnv20 B) Pure.valtypesOptT (.opt ((Pure.selAnnot ts).map .list)) :=
      typed_select20 (typedI_of_mem (i := .select ts) hc (by simp))
    exact spure_of_firesB20 ((Pure.selectFalse_iff B
      ⟨typedV_val20 _, typedV_val20 _, T.i32 _, ht⟩).2 ⟨rfl, rfl⟩)
  | @ifTrue c bt b₁ b₂ hc' =>
    obtain ⟨h₁, h₂, h₃⟩ := typed_if20 (typedI_of_mem (i := .if_ bt b₁ b₂) hc (by simp))
    exact spure_of_firesB20 ((Pure.ifTrue_iff B ⟨T.i32 _, h₁, h₂, h₃⟩).2 ⟨hc', rfl⟩)
  | @ifFalse bt b₁ b₂ =>
    obtain ⟨h₁, h₂, h₃⟩ := typed_if20 (typedI_of_mem (i := .if_ bt b₁ b₂) hc (by simp))
    exact spure_of_firesB20 ((Pure.ifFalse_iff B ⟨T.i32 _, h₁, h₂, h₃⟩).2 ⟨rfl, rfl⟩)
  | @brZero n cont vs' vs l is hl hn =>
    obtain ⟨hn', hcont, hbody⟩ := label_all20 hc
    have hr : TypedV (simEnv20 B) Pure.instrsT (.list (adminsToV (expression is))) :=
      typedV_tail20 hbody
    rw [← vals_append]
    exact spure_of_firesB20 ((Pure.brZero_iff B hn' hcont (fun v _ => typedV_val20 v) hr).2
      ⟨hl, vs', vs, rfl, hn, rfl⟩)
  | brSucc hl =>
    obtain ⟨hn', hcont, hbody⟩ := label_all20 hc
    exact spure_of_firesB20 ((Pure.brSucc_iff B hn' hcont (typedV_valsT_vals20 _)
      (typedV_labelidx20 (labelPred _)) (typedV_tail20 hbody)).2 ⟨hl, rfl⟩)
  | brIfTrue hc' =>
    exact spure_of_firesB20 ((Pure.brIfTrue_iff B (T.i32 _) (typedV_labelidx20 _)).2 ⟨hc', rfl⟩)
  | brIfFalse =>
    exact spure_of_firesB20 ((Pure.brIfFalse_iff B (T.i32 _) (typedV_labelidx20 _)).2 ⟨rfl, rfl⟩)
  | @brTableLt i ls l' l hi =>
    obtain ⟨hls, hl'⟩ := typed_brTable20 (typedI_of_mem (i := .brTable ls l') hc (by simp))
    exact spure_of_firesB20 ((Pure.brTableLt_iff B ⟨T.i32 _, hls, hl'⟩).2 ⟨_, hi, rfl⟩)
  | @brTableGe i ls l' hi =>
    obtain ⟨hls, hl'⟩ := typed_brTable20 (typedI_of_mem (i := .brTable ls l') hc (by simp))
    exact spure_of_firesB20 ((Pure.brTableGe_iff B ⟨T.i32 _, hls, hl'⟩).2 ⟨hi, rfl⟩)
  | @returnFrame n fr vs' vs is hn =>
    obtain ⟨hn', hfr, hbody⟩ := frame_all20 hc
    have hr : TypedV (simEnv20 B) Pure.instrsT (.list (adminsToV (expression is))) :=
      typedV_tail20 hbody
    rw [← vals_append]
    exact spure_of_firesB20 ((Pure.returnFrame_iff B hn' hfr (fun v _ => typedV_val20 v) hr).2
      ⟨vs', vs, rfl, hn, rfl⟩)
  | returnLabel =>
    obtain ⟨hn', hcont, hbody⟩ := label_all20 hc
    exact spure_of_firesB20 ((Pure.returnLabel_iff B hn' hcont (typedV_valsT_vals20 _)
      (typedV_tail20 hbody)).2 rfl)
  | trapVals hne =>
    exact spure_of_firesB20 ((Pure.trapVals_iff B (typedV_valsT_vals20 _)
      (typedV_tail20 hc)).2 ⟨hne, rfl⟩)
  | cvtOp hop h =>
    exact spure_of_firesB20 ((Pure.cvtOp_iff B C T (Pure.cvtTyped_simEnv20 B) hop).2 ⟨_, h, rfl⟩)
  | cvtOpTrap hop h =>
    exact spure_of_firesB20 ((Pure.cvtOpTrap_iff B C T (Pure.cvtTyped_simEnv20 B) hop).2 ⟨h, rfl⟩)
  | refIsNullTrue =>
    exact spure_of_firesB20 ((State.refIsNullTrue_iff B (typedV_ref20 _)
      (fun t _ => typedV_refType20 t)).2 ⟨⟨_, rfl⟩, rfl⟩)
  | refIsNullFalse h =>
    exact spure_of_firesB20 ((State.refIsNullFalse_iff B (typedV_ref20 _)
      (fun t _ => typedV_refType20 t)).2 ⟨h, rfl⟩)
  | localTee =>
    exact spure_of_firesB20 ((State.localTee_iff B (typedV_val20 _) (typedV_idx20 _)).2 rfl)

/-- **Subject reduction for the second fragment**: the result code is a typed `admininstr*`. -/
theorem typedV_succ_pureFrag20B {P : Profile} {is is' : List Admin}
    (hc : TypedV (simEnv20 B) adminsTy (.list (adminsToV is))) (h : PureFrag20B P is is') :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV is')) := by
  cases h with
  | selectTrue _ | selectFalse _ _ _ | localTee =>
    first
    | exact typedV_admins_val20 _
    | exact typedV_admins_append20_iff.2 ⟨typedV_admins_val20 _, typedV_admins_append20_iff.2
        ⟨typedV_admins_val20 _, typedV_admins_single20_iff.2
          (typed_localSet_of_tee20 (typedI_of_mem hc (by simp)))⟩⟩
  | @ifTrue c bt b₁ b₂ _ =>
    obtain ⟨h₁, h₂, -⟩ := typed_if20 (typedI_of_mem (i := .if_ bt b₁ b₂) hc (by simp))
    exact typedV_admins_single20_iff.2 (typed_block20 h₁ h₂)
  | @ifFalse bt b₁ b₂ =>
    obtain ⟨h₁, -, h₃⟩ := typed_if20 (typedI_of_mem (i := .if_ bt b₁ b₂) hc (by simp))
    exact typedV_admins_single20_iff.2 (typed_block20 h₁ h₃)
  | brZero _ _ =>
    obtain ⟨-, hcont, -⟩ := label_all20 hc
    exact typedV_admins_append20_iff.2
      ⟨typedV_admins_vals20 _, (typedV_admins_expression20_iff _).2 hcont⟩
  | brSucc _ =>
    exact typedV_admins_append20_iff.2 ⟨typedV_admins_vals20 _,
      typedV_admins_single20_iff.2 (typed_br20 (typedV_labelidx20 _))⟩
  | brIfTrue _ | brTableLt _ | brTableGe _ =>
    exact typedV_admins_single20_iff.2 (typed_br20 (typedV_labelidx20 _))
  | brIfFalse => exact typedV_admins_nil20
  | returnFrame _ => exact typedV_admins_vals20 _
  | returnLabel =>
    exact typedV_admins_append20_iff.2 ⟨typedV_admins_vals20 _,
      typedV_admins_single20_iff.2 typed_return20⟩
  | trapVals _ | cvtOpTrap _ _ => exact typedV_admins_trap20
  | cvtOp _ _ => exact typedV_admins_val20 (.num _)
  | refIsNullTrue | refIsNullFalse _ => exact typedV_admins_const20 _

/-- **The second pure fragment at any state.** -/
inductive PureFwd20B (P : Profile) : Config H → Config H → Prop where
  | mk {s : Store H} {f : Frame} {is is' : List Admin} (h : PureFrag20B P is is') :
      PureFwd20B P ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- **The second pure fragment is a base**, at `CvtAgree` builtins and any store condition. -/
theorem fwdBase20_pureB {P : Profile} {W : Store H → Prop} (C : Pure.CvtAgree (simEnv20 B) P) :
    FwdBase20 B hn W (PureFwd20B P) where
  sr _ _ hc h := by
    cases h with
    | mk h =>
      obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
      exact typed20_iff.2 ⟨hz, typedV_succ_pureFrag20B hcode h⟩
  fwd _ _ hc _ h := by
    cases h with
    | mk h =>
      obtain ⟨hz, hcode⟩ := typed20_iff.1 hc
      exact fwdS_pure hc (typed20_iff.2 ⟨hz, typedV_succ_pureFrag20B hcode h⟩)
        (spure_of_pureFrag20B C hcode h)

/-! ## `call` -/

/-- **`call`**, where V2's lookup is defined. -/
inductive CallFwd20 : Config H → Config H → Prop where
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
      (ha : f.module.funcs[x.toNat]? = some a) :
      CallFwd20 ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.callAddr a]⟩

/-- `CALL_ADDR a` is a typed `admininstr*`. -/
theorem typedV_admins_callAddr20 (a : Nat) :
    TypedV (simEnv20 B) adminsTy (.list (adminsToV [.callAddr a])) :=
  typedV_admins_single20_iff.2 (Pure.typedV_closedCase20 findTyp_admininstr20 rfl
    (typedV_aliasG findTyp_funcaddr20 (typedV_addr20 a _ valsOnly_empty20) _ valsOnly_empty20))

/-- **`call` is a base**, at every builtins and any store condition. -/
theorem fwdBase20_call {W : Store H → Prop} : FwdBase20 B hn W (CallFwd20 (H := H)) where
  sr _ _ hc h := by
    cases h with
    | call _ => exact typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_callAddr20 _⟩
  fwd _ _ hc _ h := by
    cases h with
    | @call s f x a ha =>
      have hz := typedV_state_of_typed20 hc
      have hc' : Typed20 (simEnv20 B) hn ⟨s, f, [.callAddr a]⟩ :=
        typed20_iff.2 ⟨(typed20_iff.1 hc).1, typedV_admins_callAddr20 _⟩
      exact fwdS_read hc hc' (sread_of_firesB20 ((State.call_iff B hn ha hz
        (typedV_idx20 _)).2 rfl))

/-! ## One forward statement, widened -/

/-- **The widened base**: pass 1's assembled base, the second pure fragment and `call`. -/
inductive FwdStep20B (P : Profile) : Config H → Config H → Prop where
  | base {c c' : Config H} (h : FwdStep20 P c c') : FwdStep20B P c c'
  | pure {c c' : Config H} (h : PureFwd20B P c c') : FwdStep20B P c c'
  | call {c c' : Config H} (h : CallFwd20 c c') : FwdStep20B P c c'

/-- Every widened base step is a V2 step. -/
theorem FwdStep20B.step {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : FwdStep20B P c c') : Step P host c c' := by
  cases h with
  | base h => exact h.step
  | pure h =>
    cases h with
    | mk h => exact .pure h.pureStep
  | call h =>
    cases h with
    | call ha => exact .read (State.call_step ha)

/-- **The widened base is a base**, at `GrowCalls20`, `NumAgree` and `CvtAgree` builtins, under
whole pages. -/
theorem fwdBase20_fwdB {P : Profile} (hG : GrowCalls20 B) (A : Pure.NumAgree (simEnv20 B) P)
    (C : Pure.CvtAgree (simEnv20 B) P) : FwdBase20 B hn WholePages (FwdStep20B (H := H) P) where
  sr c c' hc h := by
    cases h with
    | base h => exact (fwdBase20_fwd hG A).sr c c' hc h
    | pure h => exact (fwdBase20_pureB (W := WholePages) C).sr c c' hc h
    | call h => exact (fwdBase20_call (W := WholePages)).sr c c' hc h
  fwd c c' hc hw h := by
    cases h with
    | base h => exact (fwdBase20_fwd hG A).fwd c c' hc hw h
    | pure h => exact (fwdBase20_pureB C).fwd c c' hc hw h
    | call h => exact fwdBase20_call.fwd c c' hc hw h

/-- **The forward 2.0 half on the widened nested fragment** (stated and proved): at `growB`,
every step of `Nest20 (FwdStep20B P)` from a configuration with typed image and whole pages is a
step of the corrected script between the images, with a typed successor image. -/
def Task.wholeStepFwd20B : Prop :=
  ∀ (H : Type) (hn : H → String) (nd : Bool) (r : RelaxedChoice) (c c' : Config H),
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c → WholePages c.store →
    Nest20 (FwdStep20B (Profile.spec nd r)) c c' →
    Typed20 (simEnv20 (growB (Profile.spec nd r))) hn c' ∧
      Sim.Round6.Reading.SStepB (StepFix.simEnv20S (growB (Profile.spec nd r))) (configV hn c)
        (configV hn c')

/-- **`Task.wholeStepFwd20B` is proved.** -/
theorem wholeStepFwd20B : Task.wholeStepFwd20B := by
  intro H hn nd r c c' hc hw h
  have G := growLike20_growB (Profile.spec nd r)
  exact fwd_nest20 (fwdBase20_fwdB G.calls (Pure.numAgree_simEnv20 G.int G.float)
    (Pure.cvtAgree_simEnv20 G.float)) h hc hw

end Silmaril.Wasm.SpecTec.Sim20.Whole
