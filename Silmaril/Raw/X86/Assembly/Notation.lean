module

public import Silmaril.X86.Assembly.Defs
public meta import Silmaril.X86.Assembly.Defs
public import Lean

/-!
# Assembly string notation

`x86% "mov rax, rdi\nadd rax, rsi\nret"` expands to a list of ordinary
`Ext.Instr` constructor terms. `x86i% "mov rax, rdi"` expands to one instruction.
Parsing happens during macro expansion. It introduces no axiom, evaluator or
alternative semantics. Source correspondence still needs a separately checked
decoding or `Program.SourceCertificate` theorem.
-/

public meta section

namespace Silmaril.X86.Assembly

open Lean

private def constructor (typeName : Name) (name : String) : TSyntax `term :=
  ⟨mkIdent (Name.str typeName name)⟩

private def regTerm (r : Reg) : TSyntax `term :=
  let name := match r with
    | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
    | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
    | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
    | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"
  constructor ``Reg name

private def szTerm (sz : Ext.Sz) : TSyntax `term :=
  constructor ``Ext.Sz (match sz with | .d => "d" | .q => "q")

private def memTerm (m : Ext.Mem) : MacroM (TSyntax `term) := do
  let .reg base := m.base | Macro.throwError "unsupported memory base in assembly macro"
  let index ← match m.index with
    | none => `(term| none)
    | some i => `(term| some ⟨$(regTerm i.reg), $(quote i.scale.toNat), by decide⟩)
  `(term| Silmaril.X86.Ext.Mem.ofReg $(regTerm base) $index $(quote m.disp.toNat))

private def rmTerm (r : Ext.RM) : MacroM (TSyntax `term) := do
  match r with
  | .reg r => `(term| Silmaril.X86.Ext.RM.reg $(regTerm r))
  | .mem m => `(term| Silmaril.X86.Ext.RM.mem $(← memTerm m))

private def aluTerm (op : AluOp) : TSyntax `term := constructor ``AluOp (aluName op)

private def condTerm (c : Ext.Cond) : TSyntax `term :=
  constructor ``Ext.Cond ((conditionName c).drop 1).toString

private def instrTerm (i : Ext.Instr) : MacroM (TSyntax `term) := do
  match i with
  | .mov sz d s => `(term| .mov $(szTerm sz) $(← rmTerm d) $(regTerm s))
  | .load sz d s => `(term| .load $(szTerm sz) $(regTerm d) $(← memTerm s))
  | .mov8 d s => `(term| .mov8 $(regTerm d) $(← rmTerm s))
  | .store n d s =>
    let n := constructor ``Ext.Narrow (match n with | .b => "b" | .w => "w")
    `(term| .store $n $(← rmTerm d) $(regTerm s))
  | .movI sz d n => `(term| .movI $(szTerm sz) $(← rmTerm d) $(quote n.toNat))
  | .movI32 d n => `(term| .movI32 $(regTerm d) $(quote n.toNat))
  | .alu sz op d s => `(term| .alu $(szTerm sz) $(aluTerm op) $(← rmTerm d) $(regTerm s))
  | .aluR sz op d s => `(term| .aluR $(szTerm sz) $(aluTerm op) $(regTerm d) $(← rmTerm s))
  | .aluI sz op d n => `(term| .aluI $(szTerm sz) $(aluTerm op) $(← rmTerm d) $(quote n.toNat))
  | .aluI8 sz op d n => `(term| .aluI8 $(szTerm sz) $(aluTerm op) $(← rmTerm d) $(quote n.toNat))
  | .imul sz d s => `(term| .imul $(szTerm sz) $(regTerm d) $(← rmTerm s))
  | .shift sz op d count =>
    let count ← match count with
      | .cl => `(term| Silmaril.X86.Ext.Count.cl)
      | .one => `(term| Silmaril.X86.Ext.Count.one)
      | .imm n => `(term| Silmaril.X86.Ext.Count.imm $(quote n.toNat))
    let op := constructor ``Ext.ShiftOp (shiftName op)
    `(term| .shift $(szTerm sz) $op $(← rmTerm d) $count)
  | .call n => `(term| .call $(quote n.toNat))
  | .jmp n => `(term| .jmp $(quote n.toNat))
  | .jmp8 n => `(term| .jmp8 $(quote n.toNat))
  | .jcc c n => `(term| .jcc $(condTerm c) $(quote n.toNat))
  | .jcc8 c n => `(term| .jcc8 $(condTerm c) $(quote n.toNat))
  | .push r => `(term| .push $(regTerm r))
  | .pop r => `(term| .pop $(regTerm r))
  | .ret => `(term| .ret)
  | .leave => `(term| .leave)
  | .endbr64 => `(term| .endbr64)
  | .ud2 => `(term| .ud2)
  | _ => Macro.throwError "unsupported instruction in assembly macro"

private def parseTerm (source : String) (single : Bool) : MacroM (TSyntax `term) := do
  let instructions ← match parse source with
    | .ok xs => pure xs
    | .error message => Macro.throwError s!"x86 assembly: {message}"
  let terms ← instructions.toArray.mapM instrTerm
  if single then
    if h : terms.size = 1 then
      `(term| ($(terms[0]) : Silmaril.X86.Ext.Instr))
    else Macro.throwError "x86i% requires exactly one instruction"
  else `(term| ([$terms,*] : List Silmaril.X86.Ext.Instr))

/-- Read one supported x86 instruction as an ordinary `Ext.Instr` term. -/
macro "x86i% " source:str : term => parseTerm source.getString true

/-- Read a supported newline-separated listing as an ordinary `List Ext.Instr`. -/
macro "x86% " source:str : term => parseTerm source.getString false

end Silmaril.X86.Assembly
