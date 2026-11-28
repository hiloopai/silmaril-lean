# Standard ACL2 objects for X86-RUN

The Lean specialization admits the existing generated `X86-RUN` declaration over `Object` and
`objectPrimitives`. `MachineBindings` supplies three total unary functions.
The model binds `ACL2::ZP` to `Object.zp`, `ACL2::BINARY-+` to
`Object.binaryAdd`, and the literal encoding to `Object.integer (-1)`.
The standard integer projection, positive-integer characterization of NIL
`ZP`, and exact integer addition discharge all fields of `CountLaws`. The
admitted model satisfies the generated defining equation and exported
`X86-RUN-HALTED` formula, and its run returns the input state on both status
exits. Those results apply to all ACL2 objects, including counts outside the
native guard. [Lean specialization](../../Silmaril/Logic/ACL2/X86Run/Standard/Thms.lean) ·
[World export and translation](acl2-x86-run.md) ·
[Standard object profile](acl2-standard-objects.md)

## Direct unresolved bindings

These are the direct unresolved function references in the exported logical
body. All three have `logicp` true, one `X86ISA::X86` formal, and symbol-class
`:COMMON-LISP-COMPLIANT` in the pinned ACL2 8.7 certified world
(`bc6f4f49e81a0711214a8d91f0d06e0e084d2204`, `X86ISA_EXEC=nil`).

| Exported name | Arity | Lean field | Logical identity | Executable identity | Pinned source |
| --- | --- | --- | --- | --- | --- |
| `X86ISA::FAULT` | 1 | `fault` | `X86ISA::FAULT$A`, ordinary value result | `X86ISA::FAULT$C` | [`machine/state.lisp`][state] |
| `X86ISA::MS` | 1 | `ms` | `X86ISA::MS$A`, ordinary value result | `X86ISA::MS$C` | [`machine/state.lisp`][state] |
| `X86ISA::X86-FETCH-DECODE-EXECUTE` | 1 | `fetchDecodeExecute` | `X86ISA::X86-FETCH-DECODE-EXECUTE`, translated body with an `X86` stobj result | Same declared symbol, executable in ACL2 | [`machine/x86.lisp`][step] |

The `FAULT` and `MS` rows are the generated `defrstobj` exports. The
logical and executable identities come from the `X86` abstract-stobj tuples
in the certified world. The step is an ordinary logical definition whose
world entry has `non-executablep` NIL. The call in the translated run body
uses its logical meaning. [State fields][fields] · [Abstract-stobj tuple format][tuples]

The model parameters impose no stobj invariant or native-state relation. To
close the machine correspondence, supply logical definitions of both
accessors and the step, including their declaration and constraint closure,
and prove the state relation for both machine views and the environment.
The source-translation boundary is still the pinned ACL2 export and
translation checked by the original slice.

## Checks

```sh
lake build --wfail +Silmaril.Logic.ACL2.X86Run.Standard.Tests
python3 -B tools/acl2-x86isa/check_x86_run.py /path/to/fresh/x86-run.json
make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.Standard.Tests +Silmaril.Logic.ACL2.Standard.Objects.Tests +Silmaril.Logic.ACL2.Recursive.Tests'
```

The regression checks the concretely bound arithmetic, the natural count
rank, both early exits with distinguishable fixture results, and the original
generated sentence in the admitted model. It applies the standard
`natRank_decrement_lt` lemma to the exported argument order `(-1, n)`.
The axiom audit checks the public specialization and its transitive
dependencies. [Lean regressions](../../Silmaril/Logic/ACL2/X86Run/Standard/Tests.lean)

Start `saved_acl2` with `ACL2_CUSTOMIZATION=NONE` to inspect the three rows.
`NIL` in `stobjs-out` denotes an ordinary object result. [Pinned certified checkout](acl2-x86-run.md#reproduce)

```lisp
(include-book "projects/x86isa/machine/x86" :dir :system :ttags nil
              :uncertified-okp nil :defaxioms-okp nil :skip-proofs-okp nil)
:q
(let* ((world (w *the-live-state*))
       (x86 (find-symbol "X86" "X86ISA"))
       (tuples (car (absstobj-tuples-lst x86 world)))
       (*package* (find-package "KEYWORD")))
  (dolist (spelling '("FAULT" "MS" "X86-FETCH-DECODE-EXECUTE"))
    (let ((name (find-symbol spelling "X86ISA")))
      (format t "~&~s ~s ~s ~s ~s ~s~%" name (arity name world) (logicp name world)
              (getpropc name 'symbol-class nil world)
              (stobjs-out name world) (assoc name tuples)))))
```

[state]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/state.lisp#L662-L679
[fields]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/state.lisp#L222-L234
[step]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/books/projects/x86isa/machine/x86.lisp#L207
[tuples]: https://github.com/acl2/acl2/blob/bc6f4f49e81a0711214a8d91f0d06e0e084d2204/translate.lisp#L16903-L16914
