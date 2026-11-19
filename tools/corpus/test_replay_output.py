"""Live child-output boundaries consumed by the unchanged CI timing parser.

Synthetic Lake lines stay inside in-memory test sinks. They are never emitted
into a CI job's real output or used to manufacture compilation credit.
"""
import hashlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from replay_measure import measure

ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('unchanged_ci_time',ROOT/'scripts/check-ci-time.py')
ci_time=importlib.util.module_from_spec(spec)
spec.loader.exec_module(ci_time)


class ArrivalSink:
    """Deterministic logical arrival clock; ack proves forwarding before exit."""
    def __init__(self,stamp,ack=None):
        self.stamp=stamp;self.ack=ack;self.raw=bytearray();self.pending=bytearray();self.lines=[]

    def write(self,chunk):
        self.raw.extend(chunk);self.pending.extend(chunk)
        while b'\n' in self.pending:
            line,_,tail=self.pending.partition(b'\n');self.pending[:]=tail
            self.lines.append(self.stamp+' '+line.decode())
            if self.ack:self.ack.write_text('received before child exit')
        return len(chunk)

    def flush(self):pass


class LiveOutputTest(unittest.TestCase):
    def test_live_boundaries_keep_compile_union_and_runtime_credit_zero(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);ack_a=root/'ack-a';ack_b=root/'ack-b'
            a=b'\xe2\x9c\x94 [1/2] Built Fixture.A (2s)\n'
            b=b'\xe2\x9c\x94 [2/2] Built Fixture.B (2s)\n'
            # Each child phase waits until its bytes have actually reached its
            # sink. Buffered-after-exit forwarding would deadlock and time out.
            code=f'''import os,time
from pathlib import Path
os.write(1,{a[:9]!r});os.write(1,{a[9:]!r})
while not Path({str(ack_a)!r}).exists():time.sleep(0.005)
os.write(2,{b!r})
while not Path({str(ack_b)!r}).exists():time.sleep(0.005)
'''
            first=ArrivalSink('2026-01-01T00:00:02Z',ack_a)
            second=ArrivalSink('2026-01-01T00:00:06Z',ack_b)
            row=measure([sys.executable,'-c',code],stdout=root/'build.out',stderr=root/'build.err',
                        cpus=1,memory_gib=1,timeout_seconds=5,tee_stdout=first,tee_stderr=second)
            self.assertEqual(row['exit'],0)
            self.assertNotIn('output_relay_error',row['resource'])
            for stream,data,sink,file in [('stdout',a,first,'build.out'),('stderr',b,second,'build.err')]:
                self.assertEqual(bytes(sink.raw),data)
                self.assertEqual((root/file).read_bytes(),data)
                self.assertEqual(row[stream+'_sha256'],hashlib.sha256(data).hexdigest())
            start=ci_time.timestamp('2026-01-01T00:00:00Z')
            runtime_start=ci_time.timestamp('2026-01-01T00:00:08Z')
            end=ci_time.timestamp('2026-01-01T00:00:20Z')
            live=first.lines+second.lines
            self.assertEqual(ci_time.compile_seconds(live,start,end),4)
            # Demonstrate the previous collapse: both lines replayed at build
            # exit yield only2s, shifted to the post-compilation [6,8] interval.
            delayed=['2026-01-01T00:00:08Z '+line.split(' ',1)[1] for line in live]
            self.assertEqual(ci_time.compile_seconds(delayed,start,end),2)
            runtime=ArrivalSink('2026-01-01T00:00:20Z')
            message=b'PASS168 runtime including full initialization\n{"name":"core","wall_seconds":12}\n'
            observed=measure([sys.executable,'-c',f'import os;os.write(1,{message!r})'],
                             stdout=root/'run.out',stderr=root/'run.err',cpus=1,memory_gib=1,
                             timeout_seconds=5,tee_stdout=runtime,tee_stderr=io.BytesIO())
            self.assertEqual(observed['exit'],0)
            self.assertEqual(bytes(runtime.raw),message)
            self.assertEqual(ci_time.compile_seconds(live+runtime.lines,start,end),4)
            self.assertEqual(ci_time.compile_seconds(live+runtime.lines,runtime_start,end),0)
            # Thus16 of20 logical seconds count, including all12 runtime seconds.
            self.assertEqual((end-start).total_seconds()-ci_time.compile_seconds(live+runtime.lines,start,end),16)

    def test_output_failure_fails_closed_and_retains_bytes(self):
        class BrokenSink:
            def write(self,data):raise BrokenPipeError('fixture sink closed')
            def flush(self):pass
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            row=measure([sys.executable,'-c','import os,time;os.write(1,b"before failure\\n");time.sleep(30)'],
                        stdout=root/'out',stderr=root/'err',cpus=1,memory_gib=1,
                        timeout_seconds=5,tee_stdout=BrokenSink())
            self.assertNotEqual(row['exit'],0)
            self.assertEqual(row['resource']['output_relay_error'],'stdout:BrokenPipeError')
            self.assertEqual((root/'out').read_bytes(),b'before failure\n')

    def test_cli_imports_in_safe_and_isolated_python_modes(self):
        for mode in ['-P','-I']:
            for script in ['run_compiled_replays.py','benchmark_compiled_replays.py']:
                with self.subTest(mode=mode,script=script):
                    result=subprocess.run([sys.executable,mode,str(ROOT/'tools/corpus'/script),'--help'],
                                          cwd='/',capture_output=True,text=True,timeout=10)
                    self.assertEqual(result.returncode,0,result.stderr)
                    self.assertIn('usage:',result.stdout)


if __name__=='__main__':unittest.main()
