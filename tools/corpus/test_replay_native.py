"""Native entry ABI, Lake dependency invalidation and process cleanup regressions."""
import os
import io
import json
import shlex
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

from replay_native_bootstrap import inspect_initializer
from replay_measure import measure

ROOT=Path(__file__).resolve().parents[2]


class InitializerTest(unittest.TestCase):
    code='''LEAN_EXPORT lean_object* initialize_fixture_Driver(uint8_t builtin) {
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* run_main(int argc, char ** argv) {
return _lean_main();
}
'''

    def test_abi_is_exact_and_rejects_drift(self):
        self.assertEqual(inspect_initializer(self.code,'initialize_fixture_Driver'),'initialize_fixture_Driver')
        for changed in [self.code.replace('uint8_t builtin','uint64_t builtin'),
                        self.code.replace('char ** argv','char * argv'),
                        self.code.replace('_lean_main()','_lean_main(argc)'),
                        self.code+self.code,
                        self.code.replace('initialize_fixture_Driver','initialize_other')]:
            with self.subTest(changed=changed),self.assertRaises(ValueError):
                inspect_initializer(changed,'initialize_fixture_Driver')


class RuntimeValidationTest(unittest.TestCase):
    def test_actual_generated_abi_and_link_identity_guards(self):
        from run_compiled_replays import verify_integrated, TARGETS
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            for kind,(target,suffix,_) in TARGETS.items():
                generated=root/f'.lake/build/ir/tests/cerberus/CjsonArrayItem{suffix}.c'
                generated.parent.mkdir(parents=True,exist_ok=True)
                symbol=f'initialize_silmaril_tests_cerberus_CjsonArrayItem{suffix}'
                generated.write_text(InitializerTest.code.replace('initialize_fixture_Driver',symbol))
                source=root/f'tests/cerberus/CjsonArrayItem{suffix}.lean'
                source.parent.mkdir(parents=True,exist_ok=True);source.write_text('-- ABI fixture only\n')
                binary=root/f'.lake/build/bin/{target}'
                binary.parent.mkdir(parents=True,exist_ok=True);binary.write_text('not executed\n');binary.chmod(0o700)
                response=binary.with_suffix('.rsp')
                args=[str(root/'tools/corpus/replay_native_bootstrap.c'),'-DREPLAY_INITIALIZE='+symbol,'-Wl,--wrap=main']
                response.write_text(shlex.join(args))
            self.assertEqual(set(verify_integrated(root)),{'core','machine'})
            response=root/'.lake/build/bin/ci_corpus_cjson_array_item_core.rsp'
            valid=response.read_text()
            for changed in [valid.replace('--wrap=main','--wrap=other'),
                            valid.replace('ArrayItemContext','ArrayItemMachine'),
                            valid+' '+shlex.quote(str(root/'tools/corpus/replay_native_bootstrap.c')),
                            valid.replace('replay_native_bootstrap.c','untracked.c')]:
                response.write_text(changed)
                with self.assertRaises(ValueError):verify_integrated(root)

    def test_changed_validator_rejects_before_any_binary_runs(self):
        import run_compiled_replays as runner
        with tempfile.TemporaryDirectory() as d:
            directory=Path(d)
            def fake_build(command,*,stdout,stderr,**kw):
                stdout.write_bytes(b'');stderr.write_bytes(b'')
                return {'exit':0,'resource':{'rss_guard_triggered':False}}
            with patch.object(sys,'argv',['runner','--out',str(directory)]), \
                 patch.object(runner,'measure',side_effect=fake_build) as execute, \
                 patch.object(runner,'verify_integrated',side_effect=ValueError('changed initializer ABI')), \
                 patch.object(runner.signal,'signal'):
                with self.assertRaisesRegex(ValueError,'changed initializer ABI'):runner.main()
                self.assertEqual(execute.call_count,1)  # build only, never a replay
                self.assertIn('build',execute.call_args.args[0])


class CleanupTest(unittest.TestCase):
    def run_measured(self,code,directory,**kw):
        kw.setdefault('tee_stdout',io.BytesIO())
        kw.setdefault('tee_stderr',io.BytesIO())
        return measure([sys.executable,'-c',code],stdout=directory/'out',stderr=directory/'err',
                       cpus=1,memory_gib=1,**kw)

    def assert_not_running(self,pid):
        p=Path(f'/proc/{pid}/stat')
        if p.exists():self.assertEqual(p.read_text().split()[2],'Z')

    def test_timeout_kills_descendants(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);pidfile=root/'child'
            code=f"import subprocess,time; from pathlib import Path; p=subprocess.Popen(['sleep','30']); Path({str(pidfile)!r}).write_text(str(p.pid)); time.sleep(30)"
            row=self.run_measured(code,root,timeout_seconds=0.5)
            self.assertNotEqual(row['exit'],0)
            self.assertTrue(row['resource']['timeout_triggered'])
            self.assert_not_running(int(pidfile.read_text()))

    def test_failure_cleans_surviving_child(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);pidfile=root/'child'
            code=f"import subprocess; from pathlib import Path; p=subprocess.Popen(['sleep','30']); Path({str(pidfile)!r}).write_text(str(p.pid)); raise SystemExit(7)"
            row=self.run_measured(code,root)
            self.assertEqual(row['exit'],7)
            self.assert_not_running(int(pidfile.read_text()))

    def test_parent_cancellation_kills_descendants(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);pidfile=root/'child'
            code=f"import subprocess,time; from pathlib import Path; p=subprocess.Popen(['sleep','30']); Path({str(pidfile)!r}).write_text(str(p.pid)); time.sleep(30)"
            wait4=os.wait4;interrupted=False
            def cancel_once(pid,options):
                nonlocal interrupted
                if not interrupted:
                    deadline=time.monotonic()+3
                    while not pidfile.exists() and time.monotonic()<deadline:time.sleep(0.01)
                    interrupted=True
                    raise KeyboardInterrupt
                return wait4(pid,options)
            with patch('replay_measure.os.wait4',side_effect=cancel_once),self.assertRaises(KeyboardInterrupt):
                self.run_measured(code,root)
            self.assert_not_running(int(pidfile.read_text()))

    def test_sampler_error_fails_closed(self):
        with tempfile.TemporaryDirectory() as d,patch('replay_measure.process_tree_memory',side_effect=ValueError('invalid proc')):
            row=self.run_measured('import time;time.sleep(30)',Path(d))
            self.assertNotEqual(row['exit'],0)
            self.assertEqual(row['resource']['sampler_error'],'ValueError')


class LakeDependencyTest(unittest.TestCase):
    def test_bootstrap_sources_relink_and_validator_invalidates_lake_trace(self):
        lake=shutil.which('lake')
        self.assertIsNotNone(lake,'exact pinned Lake required for native invalidation regression')
        with tempfile.TemporaryDirectory() as d:
            root=Path(d)
            (root/'lean-toolchain').write_bytes((ROOT/'lean-toolchain').read_bytes())
            shutil.copyfile(ROOT/'tools/corpus/replay_native_bootstrap.c',root/'Bootstrap.c')
            (root/'Planner.py').write_text('# tracked validator fixture\n')
            (root/'Context.lean').write_text('module\npublic meta section\nnamespace Context\ndef value : String := "one"\n')
            (root/'Driver.lean').write_text('module\npublic meta import Context\npublic meta section\ndef main : IO Unit := IO.println ("driver:" ++ Context.value)\n')
            (root/'lakefile.toml').write_text('''name = "fixture"
[[lean_lib]]
name = "Context"
[[lean_exe]]
name = "driver"
root = "Driver"
needs = ["planner"]
moreLinkObjs = ["bootstrap"]
moreLinkArgs = ["-Werror", "-fstack-clash-protection", "-ffp-contract=off", "-fdata-sections", "-ffunction-sections", "-fPIC", "-fvisibility=hidden", "-O3", "-DNDEBUG", "-DLEAN_EXPORTING", "-iwithsysroot", "/include/clang", "-DREPLAY_INITIALIZE=initialize_fixture_Driver", "-Wl,--wrap=main"]
[[input_file]]
name = "bootstrap"
path = "Bootstrap.c"
text = false
[[input_file]]
name = "planner"
path = "Planner.py"
text = false
''')
            # A fresh fixture-owned cache exercises both compilation and real
            # cached restoration, without depending on any host cache contents.
            env=dict(os.environ,LEAN_NUM_THREADS='2',LAKE_ARTIFACT_CACHE='true',
                     LAKE_RESTORE_ARTIFACTS='true',LAKE_CACHE_DIR=str(root/'artifact-cache'))
            def build():
                p=subprocess.run([lake,'build','--wfail','driver'],cwd=root,env=env,
                                 capture_output=True,text=True,timeout=90)
                self.assertEqual(p.returncode,0,p.stdout+p.stderr)
                return p.stdout+p.stderr
            build()
            executable=root/'.lake/build/bin/driver'
            generated=root/'.lake/build/ir/Driver.c'
            inspect_initializer(generated.read_text(),'initialize_fixture_Driver')
            def run():return subprocess.check_output([str(executable)],cwd=root,text=True,timeout=10)
            self.assertEqual(run(),'driver:one\n')
            self.trace_evidence=[]
            def trace(label):
                module=json.loads((root/'.lake/build/lib/lean/Driver.trace').read_text())
                link=json.loads((root/'.lake/build/bin/driver.trace').read_text())
                entry={'phase':label,'module_depHash':module['depHash'],
                       'module_restored':module['synthetic'],'link_depHash':link['depHash']}
                self.trace_evidence.append(entry)
                return entry
            initial=trace('initial')
            # The identical build retains its actual keys and executable.
            previous=executable.stat().st_mtime_ns
            build();noop=trace('unchanged')
            self.assertEqual(executable.stat().st_mtime_ns,previous)
            self.assertEqual(noop['module_depHash'],initial['module_depHash'])
            self.assertEqual(noop['link_depHash'],initial['link_depHash'])
            planner=root/'Planner.py';original_planner=planner.read_text()
            changed_planner='# validator changed\n'
            planner.write_text(changed_planner);build()
            changed=trace('validator changed')
            self.assertNotEqual(changed['module_depHash'],initial['module_depHash'])
            # Revisit both keys with a populated cache. Lake legitimately emits
            # no "Built" line on restoration; key identity is the invariant.
            planner.write_text(original_planner);build()
            restored=trace('validator original restored')
            self.assertEqual(restored['module_depHash'],initial['module_depHash'])
            self.assertTrue(restored['module_restored'])
            planner.write_text(changed_planner);build()
            restored=trace('validator changed restored')
            self.assertEqual(restored['module_depHash'],changed['module_depHash'])
            self.assertTrue(restored['module_restored'])
            self.assertEqual(run(),'driver:one\n')
            previous=restored
            for filename,replace,expected in [
                ('Bootstrap.c',lambda s:s+'\n/* invalidation fixture */\n','driver:one\n'),
                ('Context.lean',lambda s:s.replace('"one"','"two"'),'driver:two\n'),
                ('Driver.lean',lambda s:s.replace('"driver:"','"updated:"'),'updated:two\n'),
            ]:
                with self.subTest(filename=filename):
                    p=root/filename;p.write_text(replace(p.read_text()));build()
                    current=trace(filename+' changed')
                    self.assertNotEqual(current['link_depHash'],previous['link_depHash'])
                    if filename!='Bootstrap.c':
                        self.assertNotEqual(current['module_depHash'],previous['module_depHash'])
                    self.assertEqual(run(),expected)
                    previous=current
            # A changed initializer cannot silently reuse the last passing binary.
            p=root/'Bootstrap.c';p.write_text(p.read_text().replace('REPLAY_INITIALIZE(1)','missing_initializer(1)'))
            bad=subprocess.run([lake,'build','--wfail','driver'],cwd=root,env=env,
                               capture_output=True,text=True,timeout=90)
            self.assertNotEqual(bad.returncode,0)


if __name__=='__main__':unittest.main()
