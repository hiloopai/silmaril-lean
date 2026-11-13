module

public import Silmaril.Compiler.Core.Verified.SubobjectTask.Defs

/-! # Pure array and member designators as local steps

Pointer arithmetic preserves the allocation id. The actual access bounds are a
separate `IntSubobject.Live` obligation; shifting a pointer alone proves no access
validity. These steps can be used inside effectful designator tasks before loads
or negative stores. No canonical semantics file is changed.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.SubobjectPointer

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches)

variable {file : Program} {labels : Labels}

/-- Shifting an allocated integer pointer preserves its id and adds four bytes per element. -/
theorem array_int (tags : Mem.Concrete.Tags) (ann : List Annot) (id addr n : Int) :
    primitive (.arrayShift (Mem.Concrete.intType ann))
      [.object (.pointer (.allocated id addr)), .object (.integer n)] tags =
      .ok (.object (.pointer (.allocated id (addr + 4 * n)))) := by
  simp [primitive, Mem.Concrete.intType, Mem.Concrete.typeLayout, Mem.Concrete.registeredIntegerLayout,
    Mem.Concrete.registeredInteger, Mem.Concrete.integerLayout, Mem.Concrete.baseWidth,
    bind, Except.bind, pure, Except.pure]

/-- A struct member designator uses the canonical layout's member offset. -/
theorem member (tags : Mem.Concrete.Tags) (tag : Sym) (name : Identifier)
    (members : List (Identifier × Ctype × Int)) (field : Identifier) (ty : Ctype)
    (off id addr : Int)
    (notUnion : (tags.lookup tag).any (fun x => match x.2 with
      | .union _ => true | _ => false) = false)
    (layout : Mem.Concrete.memberOffsets 64 tags tag = .ok members)
    (found : members.find? (fun x => Mem.Concrete.identifierEq x.1 name) = some (field, ty, off)) :
    primitive (.memberShift tag name) [.object (.pointer (.allocated id addr))] tags =
      .ok (.object (.pointer (.allocated id (addr + off)))) := by
  simp [primitive, layout, found, bind, Except.bind, pure, Except.pure]
  exact notUnion

/-- Array address computation takes local steps over arbitrary continuation frames. -/
theorem array_local (ann tann : List Annot) (p n : PE) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (wc : Bool) (id addr index : Int)
    (eval : Eval file (tagsOf file m) env (.inr [p, n])
      (.inr [.object (.pointer (.allocated id addr)), .object (.integer index)])) :
    LocalReaches file labels wc
      ⟨.pureExpr (.mk ann () (.arrayShift p (Mem.Concrete.intType tann) n)) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated id (addr + 4 * index)))), k, m⟩ := by
  have start := PureLocal.arguments_local file
    (c := .pureExpr (.mk ann () (.arrayShift p (Mem.Concrete.intType tann) n)) env) (.arrayShift (Mem.Concrete.intType tann))
    [p, n] env k m wc (labels := labels) (by simp [requestAux, awaitsScheduling])
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := wc)
    eval (.arrayShift (Mem.Concrete.intType tann)) [] k m rfl
  simp only [argState, List.nil_append] at args
  refine start.trans (args.tail (.next ?_ (LoadTask.plain_value _)))
  simp [requestAux, awaitsScheduling, array_int]

/-- Member computation takes local steps once the layout lookup is proved. -/
theorem member_local (ann : List Annot) (p : PE) (tag : Sym) (name : Identifier)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (wc : Bool) (id addr off : Int)
    (eval : Eval file (tagsOf file m) env (.inr [p])
      (.inr [.object (.pointer (.allocated id addr))]))
    (shift : primitive (.memberShift tag name) [.object (.pointer (.allocated id addr))]
      (tagsOf file m) = .ok (.object (.pointer (.allocated id (addr + off))))) :
    LocalReaches file labels wc
      ⟨.pureExpr (.mk ann () (.memberShift p tag name)) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated id (addr + off)))), k, m⟩ := by
  have start := PureLocal.arguments_local file
    (c := .pureExpr (.mk ann () (.memberShift p tag name)) env) (.memberShift tag name) [p] env k m wc
    (labels := labels) (by simp [requestAux, awaitsScheduling])
  have args := PureLocal.args_local file (tagsOf file m) (labels := labels) (wc := wc)
    eval (.memberShift tag name) [] k m rfl
  simp only [argState, List.nil_append] at args
  refine start.trans (args.tail (.next ?_ (LoadTask.plain_value _)))
  unfold tagsOf at shift
  simp [requestAux, awaitsScheduling, shift]

end Silmaril.Compile.Core.Verified.SubobjectPointer
