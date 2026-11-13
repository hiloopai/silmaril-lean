module

public import Silmaril.Compiler.Core.Verified.ExitCall.Defs

/-! # Core printf formatting and its stdout transition

These lemmas use the canonical Core dynamics and concrete memory, under arbitrary
continuations and initial memories. They do not evaluate programs in the compiler.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfFormat

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (Pointer)

/-- A format with no percent signs prints its characters and ignores surplus arguments. -/
theorem printFormat_plain (tags : Mem.Concrete.Tags) (cs : List Char)
    (hc : ∀ c ∈ cs, c ≠ '%') (args : PrintArgs) (m : Mem.Concrete.State)
    (fuel : Nat) (hf : cs.length < fuel) :
    printFormat tags fuel cs args m = .ok (String.ofList cs, m) := by
  induction cs generalizing fuel with
  | nil => cases fuel <;> simp_all [printFormat]
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hn := hc c (by simp)
      have ht : ∀ c ∈ cs, c ≠ '%' := fun c h => hc c (by simp [h])
      simp [printFormat, hn, ih ht fuel (by simp_all)]

/-- Decode a plain ASCII format supplied to the Core builtin. -/
theorem decode_format (cs : List Int) (hc : ∀ c ∈ cs, 0 ≤ c ∧ c < 128) :
    (cs.map (fun c => (.object (.integer c) : Val))).mapM
      (fun v => match v with
        | .object (.integer n) =>
            if 0 ≤ n && n < 256 then
              (Except.ok (Char.ofNat n.toNat) : Except Mem.Concrete.Failure Char)
            else throw (Mem.Concrete.Failure.unsupported "printf format character")
        | _ => throw (Mem.Concrete.Failure.unsupported "printf format value")) =
      .ok (cs.map fun c => Char.ofNat c.toNat) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have h := hc c (by simp)
    have ht : ∀ c ∈ cs, 0 ≤ c ∧ c < 128 := fun c h => hc c (by simp [h])
    rw [List.map_cons, List.mapM_cons]
    simp only [h.1, show c < 256 by omega, decide_true, Bool.true_and, ite_true,
      pure, Except.pure, bind, Except.bind]
    rw [ih ht]
    rfl

/-- The character conversion used by printf preserves ASCII codes. -/
theorem char_toNat {n : Nat} (h : n < 128) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

/-- The builtin's typed pointer arguments decode without inspecting the pointed-to values. -/
theorem decode_args (args : PrintArgs) :
    (args.map fun a => (.tuple [.ctype a.1, .object (.pointer a.2)] : Val)).mapM
      (fun v => match v with
        | .tuple [.ctype ty, .object (.pointer p)] =>
            (Except.ok (ty, p) : Except Mem.Concrete.Failure (Ctype × Pointer))
        | _ => throw (Mem.Concrete.Failure.unsupported "printf argument list")) = .ok args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    obtain ⟨ty, p⟩ := a
    simp only [List.map_cons, List.mapM_cons, pure, Except.pure, bind, Except.bind]
    rw [ih]

/-- Any successful canonical formatting run gives the builtin's stdout transition. -/
theorem builtin_of_format {file : Program} {labels : Labels} (cs : List Int)
    (hc : ∀ c ∈ cs, 0 ≤ c ∧ c < 128) (args : PrintArgs)
    (bt bt' : BaseType) (k : List Frame) (m finish : Mem.Concrete.State) (text : String)
    (hf : printFormat ⟨file.tagDefs, m.enumTypes⟩ (cs.length + 1)
      (cs.map fun c => Char.ofNat c.toNat) args m = .ok (text, finish)) :
    ReturnConst.Reaches file labels
      ⟨.apply (.builtin "printf") [.list bt (cs.map fun c => .object (.integer c)),
        .list bt' (args.map fun a => .tuple [.ctype a.1, .object (.pointer a.2)])], k, m⟩
      ⟨.value (.loaded (.specified (.integer text.length))), k,
        {finish with stdout := finish.stdout ++ text}⟩ := by
  let m' := {finish with stdout := finish.stdout ++ text}
  refine (ExitCall.scheduled_reaches file labels (m := m) (k := k)
    (c' := .commitMemory "printf" m' (.value (.loaded (.specified (.integer text.length)))))
    (k' := k) ?_ (by intro o h; cases h)).trans ?_
  · have hdec := decode_format cs hc
    have hargs := decode_args args
    simp only [List.mapM_map] at hdec hargs
    simp only [requestAux, awaitsScheduling, beq_self_eq_true, ite_true, pure, Except.pure,
      List.mapM_map]
    erw [hdec]
    simp only [bind, Except.bind]
    erw [hargs]
    simp only [List.length_map, hf]
    rfl
  · apply Actions.memory_reaches (name := "printf") (by intro o h; cases h)
    simp [request, requestAux, awaitsScheduling, m']

/-- A plain format is scheduled, then commits its stdout append. -/
theorem builtin_plain {file : Program} {labels : Labels} (cs : List Int)
    (hc : ∀ c ∈ cs, 0 ≤ c ∧ c < 128 ∧ c ≠ 37)
    (bt bt' : BaseType) (k : List Frame) (m : Mem.Concrete.State) :
    ReturnConst.Reaches file labels
      ⟨.apply (.builtin "printf") [.list bt (cs.map fun c => .object (.integer c)), .list bt' []], k, m⟩
      ⟨.value (.loaded (.specified (.integer (String.ofList (cs.map fun c => Char.ofNat c.toNat)).length))), k,
        {m with stdout := m.stdout ++ String.ofList (cs.map fun c => Char.ofNat c.toNat)}⟩ := by
  have hn : ∀ c ∈ (cs.map fun c => Char.ofNat c.toNat), c ≠ '%' := by
    intro ch hch
    obtain ⟨c, hmem, rfl⟩ := List.mem_map.mp hch
    have h := hc c hmem
    intro heq
    have he := congrArg Char.toNat heq
    rw [char_toNat (by omega)] at he
    change c.toNat = 37 at he
    omega
  exact builtin_of_format cs (fun c h => ⟨(hc c h).1, (hc c h).2.1⟩) [] bt bt' k m m _
    (by simpa using (printFormat_plain ⟨file.tagDefs, m.enumTypes⟩
      (cs.map fun c => Char.ofNat c.toNat) hn [] m (cs.length + 1) (by simp)))

/-- Signed decimal conversion reads the argument object and prints its mathematical integer. -/
theorem printConversion_d (tags : Mem.Concrete.Tags) (m finish : Mem.Concrete.State)
    (ann : List Annot) (p : Pointer) (n : Int) (rest : PrintArgs)
    (hl : Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) p =
      .ok (.integer (.signed .int) n, finish)) :
    printConversion tags m "" 'd' ((Mem.Concrete.intType ann, p) :: rest) =
      .ok (toString n, rest, finish) := by
  simp only [Mem.Concrete.intType] at hl
  simp [printConversion, printIntegerType, Mem.Concrete.intType, Core.normalizeInteger,
    Core.normalizeInteger.base, hl, bind, Except.bind, pure, Except.pure]

/-- Literal prefixes can be handled independently of later conversions. -/
theorem printFormat_prefix (tags : Mem.Concrete.Tags) (pre tail : List Char)
    (hc : ∀ c ∈ pre, c ≠ '%') (args : PrintArgs) (m finish : Mem.Concrete.State)
    (fuel : Nat) (text : String)
    (hf : printFormat tags fuel tail args m = .ok (text, finish)) :
    printFormat tags (pre.length + fuel) (pre ++ tail) args m =
      .ok (String.ofList pre ++ text, finish) := by
  induction pre with
  | nil => simpa using hf
  | cons c cs ih =>
    have hn := hc c (by simp)
    have ht : ∀ c ∈ cs, c ≠ '%' := fun c h => hc c (by simp [h])
    simp only [List.length_cons, List.cons_append, Nat.succ_add]
    simp [printFormat, hn, ih ht, String.append_assoc, bind, Except.bind, pure, Except.pure]

/-- A literal format containing one `%d`, with a plain prefix and suffix. -/
theorem printFormat_d (tags : Mem.Concrete.Tags) (pre suffix : List Char)
    (hp : ∀ c ∈ pre, c ≠ '%') (hs : ∀ c ∈ suffix, c ≠ '%')
    (m finish : Mem.Concrete.State) (ann : List Annot) (p : Pointer) (n : Int)
    (hl : Mem.Concrete.loadTyped tags m (Mem.Concrete.intType ann) p =
      .ok (.integer (.signed .int) n, finish)) :
    printFormat tags ((pre ++ '%' :: 'd' :: suffix).length + 1)
      (pre ++ '%' :: 'd' :: suffix) [(Mem.Concrete.intType ann, p)] m =
      .ok (String.ofList pre ++ (toString n ++ String.ofList suffix), finish) := by
  have hf : printFormat tags (suffix.length + 3) ('%' :: 'd' :: suffix)
      [(Mem.Concrete.intType ann, p)] m =
      .ok (toString n ++ String.ofList suffix, finish) := by
    simp [printFormat, printConversion_d tags m finish ann p n [] hl,
      printFormat_plain tags suffix hs [] finish (suffix.length + 2) (by omega),
      bind, Except.bind, pure, Except.pure]
  simpa [List.length_append, Nat.add_assoc] using
    printFormat_prefix tags pre ('%' :: 'd' :: suffix) hp _ m finish _ _ hf

end Silmaril.Compile.Core.Verified.PrintfFormat
