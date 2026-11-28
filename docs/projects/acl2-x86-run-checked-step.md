# X86-RUN with the checked logical step

`Silmaril.Logic.ACL2.X86Run.WithStep.machineBindings` combines the
[checked unary step definition](acl2-x86-step.md) with the
[concrete record specialization](acl2-x86-tlb.md). Its input is a total
`Translated.Interpretation X86Step.frontier` over the standard ACL2 object
carrier. Each of the [33 external bindings][frontier] is indexed by the
package-qualified name and arity from the pinned dependency manifest. The
wrapper supplies the interpretation of the checked step declaration to the
existing run model. [Binding definitions][defs]

The step equation identifies the `X86-FETCH-DECODE-EXECUTE` symbol **in the
admitted run model** with evaluation of the pinned checked step body under
the supplied frontier. The run equation and halted theorem use the original
recursive equation and the original exported `X86-RUN-HALTED` sentence in
that same model. [Theorems][thms]

The outer run tests use the fixed record readers from #5424. `X86ISA::FAULT`
and `X86ISA::MS` inside the step body use the supplied unary frontier
bindings. Correspondence to a common ACL2 world requires those two bindings
to agree pointwise with the run readers. The equations and halted statement
hold for every supplied frontier table, independently of that correspondence.
All 33 entries remain explicit denotations. Frontier admission, verification
of guards and full stobj correspondence remain separate obligations.

The [frontier specialization](acl2-x86-step-frontier.md) installs the two
record readers and seven pure helpers in this interface.

## Verify

```sh
python3 -IB tools/acl2-x86isa/check_step.py
python3 -IB tools/acl2-x86isa/check_x86_run.py --compare
python3 -IB tools/acl2-x86isa/check_status_accessors.py --compare
python3 -IB tools/acl2-x86isa/check_object_order.py --compare
python3 -IB tools/acl2-x86isa/check_environment.py --compare
python3 -IB tools/acl2-x86isa/check_tlb.py --compare
lake build --wfail +Silmaril.Logic.ACL2.X86Run.WithStep.Tests
PYTHONSAFEPATH=1 make check CHECK_TARGETS='+Silmaril.Logic.ACL2.X86Run.WithStep.Tests'
```

The test target audits the composition and its theorems against `propext`,
`Classical.choice` and `Quot.sound`.

[frontier]: ../../Silmaril/Logic/ACL2/X86Step/Source.lean#L55
[defs]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Defs.lean
[thms]: ../../Silmaril/Logic/ACL2/X86Run/WithStep/Thms.lean
