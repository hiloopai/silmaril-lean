#!/usr/bin/env python3
"""Plan an external full-initialization bootstrap; never edit generated drivers.

The pinned compiler's generated full initializer and run_main callback provide
all values and run the unchanged IO body at runtime. The supported ELF linker's
--wrap=main redirects only CRT entry. This is an optional measurement experiment,
not a pipeline test selection or semantic proof. Execute every plan step under
the measurement harness, including all startup and initialization costs.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shlex
import subprocess

TARGETS={
 'core':('ci_corpus_cjson_array_item_core','tests/cerberus/CjsonArrayItemContext'),
 'machine':('ci_corpus_cjson_array_item_machine','tests/cerberus/CjsonArrayItemMachine'),
 'audit-core':('ci_corpus_replay_audit_core','ReplayAuditCore'),
 'audit-machine':('ci_corpus_replay_audit_machine','ReplayAuditMachine'),
}


def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''): h.update(chunk)
    return h.hexdigest()


def inspect_initializer(code, expected=None):
    """Reject compiler ABI drift before launching the compiled IO callback."""
    symbols=re.findall(r'^LEAN_EXPORT lean_object\* (initialize_\w+)\(uint8_t builtin\) \{',code,re.M)
    callbacks=re.findall(r'^lean_object\* run_main\(int argc, char \*\* argv\) \{\s*return _lean_main\(\);\s*\}',code,re.M)
    if len(symbols)!=1 or len(callbacks)!=1 or (expected is not None and symbols[0]!=expected):
        raise ValueError('inspect changed compiler-generated initialization/callback ABI')
    return symbols[0]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--lake',default='lake')
    ap.add_argument('--audit',action='store_true')
    args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    prefix=Path(subprocess.check_output([args.lake,'env','lean','--print-prefix'],text=True).strip())
    clang=prefix/'bin/clang'
    bootstrap=Path('tools/corpus/replay_native_bootstrap.c').resolve()
    plan={'initialization':'real generated full initializer before unchanged run_main; all at runtime',
          'bootstrap_source':str(bootstrap),'bootstrap_sha256':sha(bootstrap),'steps':[],'targets':{}}
    for kind,(target,module) in TARGETS.items():
        if kind.startswith('audit-') != args.audit: continue
        source=Path('.lake/build/ir')/(module+'.c')
        response=Path('.lake/build/bin')/(target+'.rsp')
        if '-Wl,--wrap=main' in shlex.split(response.read_text()):
            raise SystemExit('Lake already links full initialization; use run_compiled_replays.py')
        code=source.read_text()
        initializer=inspect_initializer(code)
        obj=(args.out/(kind+'.o')).resolve()
        executable=(args.out/kind).resolve()
        compile_command=[str(clang),'-c','-o',str(obj),str(bootstrap),'-Werror',
            '-I',str(prefix/'include'),'-fstack-clash-protection','-ffp-contract=off',
            '-fdata-sections','-ffunction-sections','-fPIC','-fvisibility=hidden',
            '--sysroot',str(prefix),'-nostdinc','-isystem',str(prefix/'include/clang'),
            '-O3','-DNDEBUG','-DLEAN_EXPORTING','-DREPLAY_INITIALIZE='+initializer]
        # The original response file and all generated driver objects stay intact.
        link_command=[str(clang),'-o',str(executable),'@'+str(response.resolve()),
                      str(obj),'-Wl,--wrap=main']
        plan['steps'].extend([{'name':kind+'-bootstrap-c-compile','argv':compile_command},
                              {'name':kind+'-bootstrap-link','argv':link_command}])
        plan['targets'][kind]={'executable':str(executable),'initializer':initializer,
            'generated_c_sha256':sha(source),'original_link_response_sha256':sha(response),
            'generated_driver_edited':False}
    (args.out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps(plan,indent=2))


if __name__=='__main__':main()
