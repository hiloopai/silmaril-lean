module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdBytes
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.SubjRed

/-!
# Subject reduction for every pure step of V1

Pass 2 proved subject reduction for pass 1's sixteen leaves (`SubjRed.typed10_of_nest`). This
module extends it to **every** `PureStep` of V1 (`codeTy10_pure`): if the code before is typed as
`admininstr*`, so is the code after, provided every V1 value is a typed `val` (`ValTyped10`, the
one typing a numeric step needs for its fresh result).

The new pieces are:

* an instruction typed as `instr` is typed as `admininstr` (`typedV_admin_of_instr10`, the converse
  of pass 2's `typedV_instr_of_admin10`): 1.0's `admininstr` lists `instr`'s cases first;
* the `BLOCK` an `if` reduces to, rebuilt from the `IF`'s block type and branch
  (`typedV_blockOfIf10`);
* the bodies of `block` and `loop`, and the continuation of a branch, through
  `expression` (`codeTy10_expression`).

Everything else in the new code is a piece of the old code (`codeTy10_sub`), a value, `TRAP`, or
a `BR`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step PureStep value values
  expression)
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SpecTec.Sim (TypedV ValsOnly instrsT typedV_list_iff typedV_list_append)
open Silmaril.Wasm.SpecTec.Sim.IntNumeric (findCase)

set_option maxRecDepth 100000

variable {B : Builtins}

/-! ## Values -/

/-- **Every V1 value is a typed `val`** of the 1.0 script (a hypothesis here; integers are
always typed, floats need 1.0's `fN`). -/
def ValTyped10 (B : Builtins) : Prop :=
  ∀ v : Execution.Runtime.Value, TypedV (simEnv10 B) (.varT "val" []) (valV v)

/-- Code typed as `admininstr*`. -/
abbrev CodeTy10 (B : Builtins) (l : List Admin) : Prop :=
  TypedV (simEnv10 B) adminsT (.list (adminsToV l))

/-- Code all of whose elements are pieces of typed code is typed. -/
theorem codeTy10_sub {l l' : List Admin} (h : CodeTy10 B l) (hs : ∀ a ∈ l', a ∈ l) :
    CodeTy10 B l' :=
  typedV_admins_of10 fun _ ha => typedV_admin_of_mem10 h (hs _ ha)

/-- Code built from typed pieces. -/
theorem codeTy10_append {l l' : List Admin} (h : CodeTy10 B l) (h' : CodeTy10 B l') :
    CodeTy10 B (l ++ l') :=
  typedV_admins_of10 fun _ ha => (List.mem_append.1 ha).elim (typedV_admin_of_mem10 h)
    (typedV_admin_of_mem10 h')

/-- A value is typed code. -/
theorem codeTy10_value (V : ValTyped10 B) (v : Execution.Runtime.Value) :
    CodeTy10 B [value v] :=
  typedV_admins_of10 fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_admin_of_val10 (V v)

/-- One typed instruction is typed code. -/
theorem codeTy10_single {a : Admin} (h : TypedV (simEnv10 B) adminT10 (adminToV a)) :
    CodeTy10 B [a] :=
  typedV_admins_of10 fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact h

theorem codeTy10_trap : CodeTy10 B [.trap] :=
  typedV_admins_of10 fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_trap10

theorem codeTy10_br (l : LabelIdx) : CodeTy10 B [.source (.br l)] :=
  typedV_admins_of10 fun _ ha => by
    obtain rfl := List.mem_singleton.1 ha
    exact typedV_br10 l

theorem codeTy10_nil : CodeTy10 B [] := typedV_admins_of10 fun _ ha => nomatch ha

/-! ## `instr` inside `admininstr` -/

/-- A case of the first part of an appended variant is a case of the whole. -/
theorem hasTypCase_append_left {env : Env} {ρ : VarEnv} {ex : List TypCase} {op : MixopS}
    {w : Value} : ∀ {cs : List TypCase}, HasTypCase env ρ cs op w → HasTypCase env ρ (cs ++ ex) op w
  | [], h => by
    obtain ⟨t, qs, prems, hm, -⟩ := hasTypCase_mem h
    exact absurd hm (by simp)
  | .mk o t qs prems :: cs, h => by
    by_cases ho : o = op
    · exact (hasTypCase_cons_hit_iffQ ho).2 ((hasTypCase_cons_hit_iffQ ho).1 h)
    · exact (hasTypCase_cons_miss_iff ho).2 (hasTypCase_append_left ((hasTypCase_cons_miss_iff ho).1 h))

/-- **An instruction typed as `instr` is typed as `admininstr`.** -/
theorem typedV_admin_of_instr10 {i : V1.Instr}
    (h : TypedV (simEnv10 B) (.varT "instr" []) (instrToV i)) :
    TypedV (simEnv10 B) adminT10 (instrToV i) := by
  obtain ⟨ci, ex, hi, ha, -⟩ := findTyp_instrAdmin10 (B := B)
  obtain ⟨u, hu⟩ := instrToV_case10 i
  rw [hu] at h ⊢
  obtain ⟨op, w, he, hc⟩ :=
    hasTypDef_variantT_iff.1 (Sim20.Whole.hasTypDef_of_closed hi (h _ valsOnly_empty))
  obtain ⟨rfl, rfl⟩ := Value.case.inj he
  exact fun ρ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) ha
    Equiv.evalArgs_nil matchArgs_nil (hasTypCase_append_left hc)

/-- `instrsToV` is a map. -/
theorem instrsToV_map10 : ∀ is : List V1.Instr, instrsToV is = is.map instrToV
  | [] => rfl
  | i :: is => by
    show instrToV i :: instrsToV is = _
    rw [instrsToV_map10 is]
    rfl

/-- **A typed `instr*` is typed code** through `expression`. -/
theorem codeTy10_expression {is : List V1.Instr}
    (h : TypedV (simEnv10 B) instrsT (.list (instrsToV is))) : CodeTy10 B (expression is) := by
  refine typedV_admins_of10 fun a ha => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [instrsToV_map10] at h
  exact typedV_admin_of_instr10 (typedV_list_iff.1 h _ (List.mem_map_of_mem hi))

/-- One typed `instr` is a typed `instr*`. -/
theorem typedV_instrs_one10 {i : V1.Instr}
    (h : TypedV (simEnv10 B) (.varT "instr" []) (instrToV i)) :
    TypedV (simEnv10 B) instrsT (.list (instrsToV [i])) :=
  typedV_list_iff.2 fun _ hu => by
    obtain rfl := List.mem_singleton.1 hu
    exact h

theorem typedV_instrs_nil10 : TypedV (simEnv10 B) instrsT (.list (instrsToV [])) :=
  typedV_list_iff.2 fun _ hu => nomatch hu

/-! ## `if` to `block` -/

/-- **The `BLOCK` an `IF` reduces to is typed.** -/
theorem typedV_blockOfIf10 {bt : V1.BlockType} {b₁ b₂ : V1.Expr}
    (h : TypedV (simEnv10 B) adminT10 (instrToV (.if_ bt b₁ b₂))) :
    TypedV (simEnv10 B) adminT10 (instrToV (.block bt b₁)) ∧
      TypedV (simEnv10 B) adminT10 (instrToV (.block bt b₂)) := by
  obtain ⟨cs, htd, hb, -, hi⟩ := findTyp_admininstr10_ctrl (B := B)
  obtain ⟨hbt, h₁, h₂⟩ := hasTyp_tup3_inv
    (hasTyp_closedVariant_inv valsOnly_empty htd (h _ valsOnly_empty) hi)
    (fun hρ hv => typedV_list_of_scope hρ hv)
  have mk : ∀ {b : V1.Expr}, TypedV (simEnv10 B) instrsT (.list (instrsToV b)) →
      TypedV (simEnv10 B) adminT10 (instrToV (.block bt b)) := fun hb' =>
    Sim20.Pure.typedV_closedCase20 htd hb (Sim20.Whole.hasTyp_tup2G hbt hb')
  exact ⟨mk h₁, mk h₂⟩

/-! ## Labels and frames -/

/-- A typed label's continuation and body. -/
theorem label_parts10 {n : Nat} {cont : V1.Expr} {body : List Admin}
    (h : CodeTy10 B [.label n cont body]) :
    TypedV (simEnv10 B) instrsT (.list (instrsToV cont)) ∧ CodeTy10 B body := by
  have h' := typedV_admin_of_mem10 h (List.mem_singleton_self _)
  exact ⟨(label_inv10 h').2.1, (label_inv10 h').2.2⟩

/-- A typed frame's body. -/
theorem frame_body10 {n : Nat} {fr : Frame} {body : List Admin}
    (h : CodeTy10 B [.frame n fr body]) : CodeTy10 B body :=
  (frame_inv10 (typedV_admin_of_mem10 h (List.mem_singleton_self _))).2.2

/-! ## Every pure step -/

/-- Subject reduction at `block`. -/
theorem codeTy10_block {bt : V1.BlockType} {b : V1.Expr} (hc : CodeTy10 B [.source (.block bt b)]) :
    CodeTy10 B [.label bt.toList.length [] (expression b)] := by
  have hl := typedV_label10 (n := bt.toList.length) typedV_instrs_nil10
    (codeTy10_expression (block_body10 (typedV_head10 hc)))
  exact typedV_admins_of10 (by simpa using hl)

/-- Subject reduction at `loop`. -/
theorem codeTy10_loop {bt : V1.BlockType} {b : V1.Expr} (hc : CodeTy10 B [.source (.loop bt b)]) :
    CodeTy10 B [.label 0 [.loop bt b] (expression b)] := by
  have hl := typedV_head10 hc
  have hl' := typedV_label10 (n := 0) (typedV_instrs_one10 (typedV_instr_of_admin10 hl))
    (codeTy10_expression (loop_body10 hl))
  exact typedV_admins_of10 (by simpa using hl')

/-- Subject reduction at `if`: both blocks are typed. -/
theorem codeTy10_if {bt : V1.BlockType} {b₁ b₂ : V1.Expr} {c : BitVec 32}
    (hc : CodeTy10 B [value (.int .i32 c), .source (.if_ bt b₁ b₂)]) :
    CodeTy10 B [.source (.block bt b₁)] ∧ CodeTy10 B [.source (.block bt b₂)] := by
  obtain ⟨h₁, h₂⟩ := typedV_blockOfIf10 (typedV_second10 hc)
  exact ⟨codeTy10_single h₁, codeTy10_single h₂⟩

/-- **Subject reduction for every pure step of V1**, given that V1 values are typed. -/
theorem codeTy10_pure (V : ValTyped10 B) {before after : List Admin}
    (hp : PureStep before after) (hc : CodeTy10 B before) : CodeTy10 B after := by
  cases hp with
  | nop => exact codeTy10_nil
  | unreachable => exact codeTy10_trap
  | drop v => exact codeTy10_nil
  | selectZero a b _ => exact codeTy10_sub hc (by simp)
  | selectNonzero a b _ c _ => exact codeTy10_sub hc (by simp)
  | block bt body => exact codeTy10_block hc
  | loop bt body => exact codeTy10_loop hc
  | ifZero bt l r => exact (codeTy10_if hc).2
  | ifNonzero bt l r c _ => exact (codeTy10_if hc).1
  | brIfZero l => exact codeTy10_nil
  | brIfNonzero l c _ => exact codeTy10_br l
  | brTable ls d c => exact codeTy10_br _
  | labelDone n cont vs => exact (label_parts10 hc).2
  | labelBranch n cont extra vs tail _ =>
    obtain ⟨hk, hb⟩ := label_parts10 hc
    exact codeTy10_append (codeTy10_sub hb (by simp_all)) (codeTy10_expression hk)
  | labelBranchOuter n cont vs tail l _ =>
    exact codeTy10_append (codeTy10_sub (label_parts10 hc).2 (by simp_all)) (codeTy10_br _)
  | labelReturn n cont vs tail =>
    exact codeTy10_sub (label_parts10 hc).2 fun _ ha => List.mem_append_left _ ha
  | frameDone n fr vs _ => exact frame_body10 hc
  | frameReturn n fr extra vs tail _ => exact codeTy10_sub (frame_body10 hc) (by simp_all)
  | trapValues v vs tail => exact codeTy10_trap
  | trapTail i tail => exact codeTy10_trap
  | labelTrap n cont => exact codeTy10_trap
  | frameTrap n fr => exact codeTy10_trap
  | localTee i v =>
    exact codeTy10_append (l := [value v, value v]) (codeTy10_sub hc (by simp))
      (codeTy10_single (typedV_localSet10 i))
  | intUnary t op x => exact codeTy10_value V _
  | intBinary t op x y z _ => exact codeTy10_value V _
  | intBinaryTrap t op x y e _ => exact codeTy10_trap
  | intTest t op x => exact codeTy10_value V _
  | intRel t op x y => exact codeTy10_value V _
  | floatUnary t op x y _ => exact codeTy10_value V _
  | floatBinary t op x y z _ => exact codeTy10_value V _
  | floatRel t op x y => exact codeTy10_value V _
  | convert op x y _ => exact codeTy10_value V _
  | convertTrap op x e _ => exact codeTy10_trap

end Silmaril.Wasm.SpecTec.Sim10.Whole
