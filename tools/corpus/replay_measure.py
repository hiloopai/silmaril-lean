"""Linux child-process measurements with CPU affinity and a sampled RSS guard.

The RSS guard observes this child and its descendants; it is not cgroup isolation.
Shared pages may be counted more than once. No host/kernel setting is changed.
"""
from pathlib import Path
import hashlib
import os
import signal
import subprocess
import threading
import time


def process_tree_memory(pid, *, proc=Path('/proc'), page_kib=None):
    """Count each Linux thread group once, including all its task children.

    Some proc implementations expose thread IDs in children lists. Those IDs
    share their leader's memory and must not each contribute another RSS copy.
    RSS may still double-count shared pages between distinct processes.
    """
    if page_kib is None:
        page_kib=os.sysconf('SC_PAGE_SIZE')//1024
    pending=[pid];seen=set();groups=set();rss=0;virtual=0
    while pending:
        p=pending.pop()
        if p in seen: continue
        seen.add(p)
        try:
            status=(proc/str(p)/'status').read_text().splitlines()
            group=int(next(line.split(':',1)[1] for line in status if line.startswith('Tgid:')))
            if group in groups: continue
            fields=(proc/str(group)/'statm').read_text().split()
            groups.add(group)
            rss+=int(fields[1])*page_kib
            virtual=max(virtual,int(fields[0])*page_kib)
            for task in (proc/str(group)/'task').iterdir():
                try: pending.extend(int(c) for c in (task/'children').read_text().split())
                except FileNotFoundError: pass
        except (FileNotFoundError,ProcessLookupError): pass
    return rss,virtual,len(groups)


def measure(command, *, stdout, stderr, cpus=8, memory_gib=32, env=None, timeout_seconds=None, tee_stdout=None, tee_stderr=None):
    allowed=sorted(os.sched_getaffinity(0))[:cpus]
    if len(allowed)!=cpus: raise ValueError('insufficient CPUs for affinity')
    page_kib=os.sysconf('SC_PAGE_SIZE')//1024
    stop=threading.Event()
    sampled={'peak_tree_rss_kib':0,'peak_process_virtual_kib':0,'rss_guard_triggered':False,'sample_seconds':0.05}
    def child_setup():
        os.setsid()
        os.sched_setaffinity(0,allowed)
        # Lean's allocator may reserve large virtual arenas; virtual size is not
        # physical memory. The guard below observes RSS instead of RLIMIT_AS.
    with stdout.open('wb') as out,stderr.open('wb') as err:
        began=time.monotonic()
        process=subprocess.Popen(command,stdout=subprocess.PIPE if tee_stdout is not None else out,
                                 stderr=subprocess.PIPE if tee_stderr is not None else err,
                                 env=env,preexec_fn=child_setup)
        relays=[]
        def relay(source,log,sink,stream):
            try:
                while chunk:=os.read(source.fileno(),65536):
                    log.write(chunk);log.flush()
                    sink.write(chunk);sink.flush()
            except Exception as error:
                sampled['output_relay_error']=stream+':'+type(error).__name__
                try: os.killpg(process.pid,signal.SIGKILL)
                except ProcessLookupError: pass
            finally:
                source.close()
        for source,log,sink,stream in [(process.stdout,out,tee_stdout,'stdout'),
                                       (process.stderr,err,tee_stderr,'stderr')]:
            if sink is not None:
                thread=threading.Thread(target=relay,args=(source,log,sink,stream),daemon=True)
                thread.start();relays.append(thread)
        def sample():
            while not stop.is_set():
                if timeout_seconds is not None and time.monotonic()-began >= timeout_seconds:
                    sampled['timeout_triggered']=True
                    try: os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    return
                try:
                    rss,virtual,count=process_tree_memory(process.pid,page_kib=page_kib)
                except Exception as error:
                    sampled['sampler_error']=type(error).__name__
                    try: os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    return
                sampled['peak_process_virtual_kib']=max(sampled['peak_process_virtual_kib'],virtual)
                sampled['peak_process_count']=max(sampled.get('peak_process_count',0),count)
                sampled['peak_tree_rss_kib']=max(sampled['peak_tree_rss_kib'],rss)
                if rss>memory_gib*1024**2:
                    sampled['rss_guard_triggered']=True
                    try: os.killpg(process.pid,signal.SIGKILL)
                    except ProcessLookupError: pass
                    return
                stop.wait(sampled['sample_seconds'])
        watcher=threading.Thread(target=sample,daemon=True);watcher.start()
        try:
            _,status,usage=os.wait4(process.pid,0)
            process.returncode=os.waitstatus_to_exitcode(status)
        except BaseException:
            try: os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            _,status,usage=os.wait4(process.pid,0)
            process.returncode=os.waitstatus_to_exitcode(status)
            raise
        finally:
            # Normal exit, failure, timeout or parent cancellation cannot leave
            # a still-running descendant from this measured process group.
            try: os.killpg(process.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            stop.set();watcher.join()
            for thread in relays:thread.join()
        elapsed=time.monotonic()-began
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    return {'argv':command,'wall_seconds':elapsed,'exit':process.returncode,
            'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr),
            'stdout_bytes':stdout.stat().st_size,'stderr_bytes':stderr.stat().st_size,
            'resource':{'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,
                        'max_rss_kib':usage.ru_maxrss,'major_faults':usage.ru_majflt,
                        'minor_faults':usage.ru_minflt,'voluntary_switches':usage.ru_nvcsw,
                        'involuntary_switches':usage.ru_nivcsw,**sampled,
                        'cpu_affinity':allowed,'rss_guard_gib':memory_gib,
                        'method':'wait4 plus sampled descendant RSS sum, deduplicated by Linux Tgid; not a cgroup/hard aggregate memory limit'}}
