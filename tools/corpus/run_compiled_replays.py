#!/usr/bin/env python3
"""Build and explicitly execute the two unchanged compiled corpus IO drivers.

Sequential execution bounds aggregate resources without concurrent address
spaces. Lake tracks the driver/import/toolchain and bootstrap/support inputs;
this command always asks Lake to validate freshness before any executable runs.
No replay verdict is cached. Observations are not semantic proofs.
"""
import argparse
import json
import os
from pathlib import Path
import shlex
import signal
import sys

# Import only the script's own resolved repository directory, including under
# Python -P/-I. Do not re-enable cwd/PYTHONPATH or relax the host's safe-path mode.
sys.path.insert(0,str(Path(__file__).resolve().parent))
from replay_measure import measure
from replay_native_bootstrap import inspect_initializer, sha

TARGETS = {
    'core': ('ci_corpus_cjson_array_item_core', 'Context', 168),
    'machine': ('ci_corpus_cjson_array_item_machine', 'Machine', 420),
}


def verify_integrated(root=Path('.'), *, audit=False):
    """Validate actual generated ABI and link inputs; never repair or patch them."""
    result = {}
    for kind, (target, suffix, count) in TARGETS.items():
        module=f'ReplayAudit{kind.title()}' if audit else f'tests/cerberus/CjsonArrayItem{suffix}'
        if audit: target=f'ci_corpus_replay_audit_{kind}'
        source=root/f'.lake/build/ir/{module}.c'
        response=root/f'.lake/build/bin/{target}.rsp'
        executable=root/f'.lake/build/bin/{target}'
        expected='initialize_silmaril_'+module.replace('/','_')
        inspect_initializer(source.read_text(), expected)
        args=shlex.split(response.read_text())
        required=['-DREPLAY_INITIALIZE='+expected, '-Wl,--wrap=main']
        bootstrap=[a for a in args if Path(a).resolve()==(root/'tools/corpus/replay_native_bootstrap.c').resolve()]
        if len(bootstrap)!=1:
            raise ValueError(f'{kind}: missing/duplicate tracked C bootstrap')
        if any(args.count(arg)!=1 for arg in required):
            raise ValueError(f'{kind}: missing/duplicate generated link bootstrap inputs')
        if not executable.is_file() or not os.access(executable,os.X_OK):
            raise ValueError(f'{kind}: missing executable')
        result[kind]={'path':str(executable.resolve()), 'cases':count,
                      'driver_sha256':sha(root/(f'build/corpus-replay-audit/{module}.lean' if audit else module+'.lean')),
                      'generated_c_sha256':sha(source), 'link_response_sha256':sha(response),
                      'executable_sha256':sha(executable)}
    return result


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lake',default='lake')
    ap.add_argument('--out',type=Path,default=Path('build/compiled-replay-results'))
    args=ap.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    # Inherit tighter outer affinity/thread/cgroup/rlimit restrictions. No host changes.
    cpus=min(8,len(os.sched_getaffinity(0)),int(os.environ.get('LEAN_NUM_THREADS','8')))
    if cpus < 1: raise ValueError('LEAN_NUM_THREADS must be positive')
    env=dict(os.environ,LEAN_NUM_THREADS=str(cpus))
    summary={'sequential':True,'proof':False,'steps':[]}
    def save():
        (args.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    def run(name,command):
        row=measure(command,stdout=args.out/(name+'.stdout'),stderr=args.out/(name+'.stderr'),
                    cpus=cpus,memory_gib=32,env=env,timeout_seconds=900,
                    tee_stdout=sys.stdout.buffer,tee_stderr=sys.stderr.buffer)
        row['name']=name;summary['steps'].append(row);save()
        # Genuine child bytes are teed as they arrive, never replayed after exit.
        # GitHub's arrival timestamps delimit the unchanged parser's intervals.
        print(json.dumps(row),flush=True)
        if row['exit'] or row['resource'].get('sampler_error') or row['resource'].get('timeout_triggered') or row['resource'].get('output_relay_error') or row['resource']['rss_guard_triggered']:
            raise RuntimeError(f'{name} failed; see retained logs')
    def cancel(signum,frame):
        raise InterruptedError(f'replay runner received signal {signum}')
    for sig in (signal.SIGTERM,signal.SIGINT,signal.SIGHUP):signal.signal(sig,cancel)
    save()
    run('lake-build',[args.lake,'build','--wfail',*[v[0] for v in TARGETS.values()]])
    summary['drivers']=verify_integrated();save()
    for kind,driver in summary['drivers'].items():
        run(kind,[driver['path']])
        if not (args.out/(kind+'.stdout')).read_text().startswith(f"PASS{driver['cases']} "):
            raise RuntimeError(f'{kind}: missing original case-count summary')
    summary['passed']=True;save()


if __name__=='__main__': main()
