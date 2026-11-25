# Typed renumbering of RVSDG translation units

This extends the [interprocedural graph](rvsdg-interprocedural.md) and its
inductive bindings using the typed endpoint maps from
[#2228](https://github.com/hiloopai/silmaril-lean/pull/2228) and
[the nested renumbering development](rvsdg-nested-isomorphism.md).
The structural interfaces follow Reissmann, Meyer, Bahmann and
Själander, *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §§4.2.1–4.2.4. The PDF SHA-256 is
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

An ω graph renumbering pairs vertices by a bijection. Both graphs have
the same typed import and export signatures. The map rewrites the
producer vertex of an edge while retaining its output port, and it
keeps argument origins at their existing import positions. The
paired vertices have the same kind and typed interface. λ keeps its
full function signature and compares its ordered captures and nested
body. δ keeps its global value sort and compares its ordered captures
and primitive/γ initializer. φ keeps its ordered member interfaces
and compares its outer captures, member captures, and λ bodies.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Isomorphism/Defs.lean)

The term relation reads the actual bindings in each region and checks
its endpoint wires, node kinds and positional children directly.
λ bodies use this relation on nested primitive, γ and θ terms. A δ
initializer uses the inductive inclusion of primitive/γ terms into
that nested language. Its graph renumbering both preserves and reflects
the same endpoint evidence under this inclusion. The graph relation
uses its own vertex tables and child graphs. The bridge transports the
same proposed ω bijection through encoding and linearization.
The existing exact round trips describe a fixed numbering.
[Nested term definitions](../../Silmaril/SSA/RVSDG/NestedTheta/Isomorphism/Terms/Defs.lean) ·
[Nested bridge](../../Silmaril/SSA/RVSDG/NestedTheta/Isomorphism/Terms/Thms.lean)
[Theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Isomorphism/Thms.lean)

In this φ representation a recursion argument, the physical λ
definition, the region result and the external φ output share a member
slot. `Phi.member_number_eq` proves that preserving the ordered
results forces the physical member map to be the identity. Member bodies
can use independently chosen numberings. Renumbering physical λ vertices
separately from the recursion slots would require representing that
association explicitly. The theorem reasons about the syntax and its
translations. Runtime identity and linking invariance are separate
questions.

The fixture swaps independent δ and φ definitions in ω, swaps two
vertices in the δ initializer, and renumbers the primitive and apply
producers feeding a φ member's λ body. The wrapper's capture of the
second φ output and an import re-export keep their ports. The body witnesses start from the inductive bindings. The negative
checks reject switching same-typed recursion arguments or export slots
and exchanging physical φ definitions under fixed result origins.
[Fixture](../../tests/ssa/RVSDGInterproceduralIsomorphism.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterproceduralIsomorphism.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms +Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms'
```
