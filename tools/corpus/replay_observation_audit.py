#!/usr/bin/env python3
"""Generate separately timed per-case instrumentation of unchanged IO drivers.

The original files are not edited. The generated copies retain their assertion
bodies, case matrices and negative checks; added IO records the observed fields.
These are supplemental native/interpreter comparisons, not timed replacements
for the unchanged drivers and not semantic proofs. No #eval is introduced.
"""
import hashlib
import json
from pathlib import Path

DRIVERS = {
    "Core": Path("tests/cerberus/CjsonArrayItemContext.lean"),
    "Machine": Path("tests/cerberus/CjsonArrayItemMachine.lean"),
}
CORE = '''          let auditAddresses := (List.range ((n.val+2)*64)).map (input.base+·) ++ (List.range 12).map (4096+·)
          let auditBytes := auditAddresses.map fun address =>
            (address, before.memory.bytes.lookup (Int.ofNat address), after.bytes.lookup (Int.ofNat address),
              before.memory.pointerBytes.lookup (Int.ofNat address), after.pointerBytes.lookup (Int.ofNat address))
          let auditAllocations := (List.range (n.val+4)).map fun id =>
            (id, reprStr (before.memory.allocations.lookup (Int.ofNat id)), reprStr (after.allocations.lookup (Int.ofNat id)),
              before.memory.dead.contains (Int.ofNat id), after.dead.contains (Int.ofNat id))
          let auditPrivateDead := (List.range after.nextId.toNat).filterMap fun id =>
            if (Int.ofNat id) >= before.memory.nextId then some (id, after.dead.contains (Int.ofNat id)) else none
          IO.println s!"OBS core|{n.val}|{index}|{seed.val}|{isNull}|{(observation result.ending).json.compress}|{reprStr auditAllocations}|{reprStr auditBytes}|{reprStr auditPrivateDead}|{reprStr (before.memory.stdout,after.stdout)}|{after.enumTypes == before.memory.enumTypes}|{after.functions == before.memory.functions}|forgeries={reprStr (Context.pointerWord input (.loaded (.specified (.pointer (.allocated 0 input.base)))))}:{reprStr (Context.pointerWord input (.loaded (.specified (.pointer (.allocated 2 (input.base+8))))))}"
'''
MACHINE = '''     let auditRegisters := ([Reg.rax,.rcx,.rdx,.rbx,.rsp,.rbp,.rsi,.rdi,.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]).map fun r =>
       (r.toBitVec.toNat,(before.core.read r).toNat,(after.core.read r).toNat)
     let auditAddresses := ((List.range ((n.val+2)*64)).map (base+·) ++
       (List.range code.length).map (address+·) ++ (List.range 256).map (sp-128+·)).filter fun a => !(sp-72 ≤ a && a < sp)
     let auditBytes := auditAddresses.map fun a => (a,(before.memory.bytes.get? a).map (·.toNat),(after.memory.bytes.get? a).map (·.toNat))
     IO.println s!"OBS machine|{n.val}|{index}|{seed.val}|{isNull}|{reprStr auditRegisters}|rip={after.core.rip.toNat}|flags={reprStr after.core.flags}|fs={after.core.fsBase.toNat}|regions={reprStr after.memory.regions}|keys={after.memory.bytes.size}|{reprStr auditBytes}"
'''

def generate():
    root = Path("build/corpus-replay-audit")
    root.mkdir(parents=True, exist_ok=True)
    manifest = {}
    for kind, source in DRIVERS.items():
        original = source.read_text()
        boundary = ('  ' if kind == 'Core' else ' ') + 'IO.println "PASS'
        assert original.count(boundary) == 1, 'driver changed: inspect instrumentation boundary'
        injected = original.replace(boundary, (CORE if kind == 'Core' else MACHINE)+boundary)
        if kind == 'Core':
            old = '            match (run F.file ∅ 2000000 invalid).ending with'
            new = '''            let auditInvalid := (run F.file ∅ 2000000 invalid).ending
            IO.println s!"NEG core|{n.val}|{index}|{seed.val}|{(observation auditInvalid).json.compress}"
            match auditInvalid with'''
            assert injected.count(old) == 1, 'driver changed: inspect negative instrumentation'
            injected = injected.replace(old, new)
            assert injected.replace(CORE, '').replace(new, old) == original
            # The same pure execution remains evaluated once; only its result is named/logged.
        else:
            assert injected.replace(MACHINE, '') == original
        target = root / f'ReplayAudit{kind}.lean'
        target.write_text(injected)
        manifest[kind] = {'source': str(source), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                          'generated': str(target), 'generated_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                          'policy': 'assertions/case matrix unchanged; supplemental IO only; runtime, not #eval'}
    (root/'sources.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return manifest
if __name__ == '__main__':
    print(json.dumps(generate(), indent=2))
