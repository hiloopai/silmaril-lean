//! Running a litmus test natively: fixed-address data pages, RX code pages holding the corpus
//! bytes, one pinned thread per litmus thread, a spin barrier per iteration and randomised
//! small delays.
//!
//! Linux x86-64 only. The libc symbols are declared here (std links libc), so the crate has no
//! dependencies.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use crate::corpus::{Outcome, Test};
use crate::wrap;

/// First data address of the corpus layout (`litmus-x86`'s `model::BASE`).
pub const DATA_BASE: u64 = 0x10000;
/// Length of the fixed data mapping.
pub const DATA_LEN: usize = 0x10000;
const PAGE: usize = 4096;

const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const PROT_EXEC: i32 = 4;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_FIXED_NOREPLACE: i32 = 0x10_0000;

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn sched_setaffinity(pid: i32, size: usize, mask: *const u64) -> i32;
    fn sched_getaffinity(pid: i32, size: usize, mask: *mut u64) -> i32;
}

/// An anonymous private mapping, unmapped on drop.
pub struct Mapping {
    base: *mut u8,
    len: usize,
}

// SAFETY: the mapping is plain memory owned by this value; threads only access it through
// the test code and the coordinator protocol below, which orders accesses by the barrier.
unsafe impl Send for Mapping {}
// SAFETY: as above.
unsafe impl Sync for Mapping {}

impl Drop for Mapping {
    fn drop(&mut self) {
        // SAFETY: `base`/`len` are exactly a mapping created by `mmap` and not yet unmapped.
        unsafe {
            munmap(self.base, self.len);
        }
    }
}

impl Mapping {
    /// The fixed RW data mapping at `DATA_BASE`. Fails if anything is mapped there.
    pub fn data() -> Result<Mapping, String> {
        // SAFETY: MAP_FIXED_NOREPLACE never replaces an existing mapping; the result is checked.
        let p = unsafe {
            mmap(
                DATA_BASE as *mut u8,
                DATA_LEN,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE,
                -1,
                0,
            )
        };
        if p as isize == -1 || p as u64 != DATA_BASE {
            if p as isize != -1 {
                // SAFETY: `p` is a fresh mapping of `DATA_LEN` bytes at another address.
                unsafe {
                    munmap(p, DATA_LEN);
                }
            }
            return Err(format!(
                "cannot map {DATA_LEN:#x} bytes at {DATA_BASE:#x} (vm.mmap_min_addr or an existing mapping): {}",
                std::io::Error::last_os_error()
            ));
        }
        Ok(Mapping {
            base: p,
            len: DATA_LEN,
        })
    }

    /// An executable mapping at fixed addresses: `bodies[k]` at `bases[k]`. The bases must be
    /// page-aligned and the bodies must not overlap; nothing may be mapped there already
    /// (`MAP_FIXED_NOREPLACE`).
    pub fn fixed_code(bases: &[u64], bodies: &[Vec<u8>]) -> Result<Mapping, String> {
        let lo = *bases.iter().min().ok_or("no threads")?;
        let mut hi = lo;
        for (b, f) in bases.iter().zip(bodies) {
            if b % PAGE as u64 != 0 {
                return Err(format!("code base {b:#x} is not page-aligned"));
            }
            hi = hi.max(b + (f.len().div_ceil(PAGE).max(1) * PAGE) as u64);
        }
        let mut spans: Vec<(u64, u64)> = bases
            .iter()
            .zip(bodies)
            .map(|(b, f)| (*b, b + f.len() as u64))
            .collect();
        spans.sort();
        if spans.windows(2).any(|w| w[0].1 > w[1].0) {
            return Err("thread code regions overlap".into());
        }
        let len = (hi - lo) as usize;
        // SAFETY: MAP_FIXED_NOREPLACE never replaces an existing mapping; the result is checked.
        let p = unsafe {
            mmap(
                lo as *mut u8,
                len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE,
                -1,
                0,
            )
        };
        if p as isize == -1 || p as u64 != lo {
            if p as isize != -1 {
                // SAFETY: `p` is a fresh mapping of `len` bytes at another address.
                unsafe {
                    munmap(p, len);
                }
            }
            return Err(format!(
                "cannot map code at {lo:#x}: {}",
                std::io::Error::last_os_error()
            ));
        }
        let m = Mapping { base: p, len };
        for (b, f) in bases.iter().zip(bodies) {
            // SAFETY: `[b, b + f.len())` lies inside `[lo, hi)`, the RW mapping just created.
            unsafe {
                std::ptr::copy_nonoverlapping(f.as_ptr(), p.add((b - lo) as usize), f.len());
            }
        }
        // SAFETY: changes protection of exactly the mapping created above.
        if unsafe { mprotect(p, len, PROT_READ | PROT_EXEC) } != 0 {
            return Err(format!("mprotect: {}", std::io::Error::last_os_error()));
        }
        Ok(m)
    }

    /// An executable mapping holding `funcs`, each on its own page. Returns the mapping and
    /// the entry address of each function.
    pub fn code(funcs: &[Vec<u8>]) -> Result<(Mapping, Vec<usize>), String> {
        let pages: Vec<usize> = funcs
            .iter()
            .map(|f| f.len().div_ceil(PAGE).max(1))
            .collect();
        let len = pages.iter().sum::<usize>() * PAGE;
        // SAFETY: a fresh anonymous mapping at a kernel-chosen address; the result is checked.
        let p = unsafe {
            mmap(
                std::ptr::null_mut(),
                len,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        if p as isize == -1 {
            return Err(format!("mmap code: {}", std::io::Error::last_os_error()));
        }
        let m = Mapping { base: p, len };
        let mut entries = Vec::new();
        let mut off = 0;
        for (f, n) in funcs.iter().zip(&pages) {
            // SAFETY: `off + f.len() <= len`, inside the RW mapping just created.
            unsafe {
                std::ptr::copy_nonoverlapping(f.as_ptr(), p.add(off), f.len());
            }
            entries.push(p as usize + off);
            off += n * PAGE;
        }
        // SAFETY: changes protection of exactly the mapping created above.
        if unsafe { mprotect(p, len, PROT_READ | PROT_EXEC) } != 0 {
            return Err(format!("mprotect: {}", std::io::Error::last_os_error()));
        }
        Ok((m, entries))
    }
}

/// The CPUs this process may run on.
fn allowed_cpus() -> Vec<usize> {
    let mut mask = [0u64; 16];
    // SAFETY: the kernel writes at most `size_of_val(&mask)` bytes into `mask`.
    let r = unsafe { sched_getaffinity(0, std::mem::size_of_val(&mask), mask.as_mut_ptr()) };
    if r != 0 {
        return Vec::new();
    }
    (0..1024)
        .filter(|c| mask[c / 64] >> (c % 64) & 1 == 1)
        .collect()
}

fn read_id(cpu: usize, what: &str) -> Option<u64> {
    std::fs::read_to_string(format!("/sys/devices/system/cpu/cpu{cpu}/topology/{what}"))
        .ok()?
        .trim()
        .parse()
        .ok()
}

/// One allowed logical CPU per physical core (the lowest-numbered sibling), with its
/// (package, core) id.
pub fn physical_cores() -> Vec<(usize, u64, u64)> {
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for c in allowed_cpus() {
        let (Some(pkg), Some(core)) = (read_id(c, "physical_package_id"), read_id(c, "core_id"))
        else {
            continue;
        };
        if seen.insert((pkg, core)) {
            out.push((c, pkg, core));
        }
    }
    out
}

fn pin(cpu: usize) -> Result<(), String> {
    let mut mask = [0u64; 16];
    mask[cpu / 64] |= 1 << (cpu % 64);
    // SAFETY: `mask` is a valid cpu set of `size_of_val(&mask)` bytes; pid 0 is this thread.
    let r = unsafe { sched_setaffinity(0, std::mem::size_of_val(&mask), mask.as_ptr()) };
    if r == 0 {
        Ok(())
    } else {
        Err(format!(
            "sched_setaffinity({cpu}): {}",
            std::io::Error::last_os_error()
        ))
    }
}

/// A sense-reversing spin barrier.
struct Barrier {
    n: usize,
    count: AtomicUsize,
    epoch: AtomicUsize,
}

impl Barrier {
    fn wait(&self) {
        let g = self.epoch.load(Ordering::Acquire);
        if self.count.fetch_add(1, Ordering::AcqRel) + 1 == self.n {
            self.count.store(0, Ordering::Relaxed);
            self.epoch.store(g.wrapping_add(1), Ordering::Release);
        } else {
            while self.epoch.load(Ordering::Acquire) == g {
                std::hint::spin_loop();
            }
        }
    }
}

/// xorshift64*; deterministic per (seed, test, thread).
struct Rng(u64);

impl Rng {
    fn new(seed: u64, test: usize, thread: usize) -> Rng {
        let mut s = seed
            ^ 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(test as u64 + 1)
            ^ 0xbf58_476d_1ce4_e5b9u64.wrapping_mul(thread as u64 + 1);
        if s == 0 {
            s = 1;
        }
        Rng(s)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }
}

/// A delay of about `n` loop iterations (no memory accesses, no fences).
#[inline(never)]
fn delay(n: u64) {
    let mut i = 0u64;
    while i < n {
        i = std::hint::black_box(i + 1);
    }
}

/// Harness parameters for one test.
#[derive(Clone, Debug)]
pub struct Params {
    /// Stop after this many iterations (if set).
    pub iters: Option<u64>,
    /// Stop after this much time (always applies, as a cap).
    pub time: Duration,
    pub seed: u64,
    /// Maximum random delay before the test code, in loop iterations.
    pub delay: u64,
    /// The logical CPU of each litmus thread.
    pub cpus: Vec<usize>,
}

/// The result of running one test.
#[derive(Clone, Debug)]
pub struct Run {
    pub iterations: u64,
    pub elapsed: Duration,
    /// `true` if the time cap ended a fixed-iteration run early.
    pub capped: bool,
    pub hist: BTreeMap<Outcome, u64>,
}

/// Run one test natively. `index` only feeds the per-test seed.
pub fn run(test: &Test, index: usize, p: &Params, data: &Mapping) -> Result<Run, String> {
    let n = test.threads.len();
    if p.cpus.len() < n {
        return Err(format!(
            "{}: {n} threads but only {} CPUs assigned",
            test.name,
            p.cpus.len()
        ));
    }
    for l in &test.locs {
        if l.addr < DATA_BASE || l.addr + l.init.len() as u64 > DATA_BASE + DATA_LEN as u64 {
            return Err(format!(
                "{}: location {} outside the data mapping",
                test.name, l.name
            ));
        }
    }
    // Position-independent code runs inside one wrapper function per thread. Code with a
    // `code_base` (rip-relative operands) runs at that address, entered from a stub.
    let fixed: Vec<u64> = test.threads.iter().filter_map(|t| t.code_base).collect();
    let _fixed_code = if fixed.is_empty() {
        None
    } else if fixed.len() == n {
        let bodies: Vec<Vec<u8>> = test.threads.iter().map(|t| wrap::body(&t.code)).collect();
        Some(Mapping::fixed_code(&fixed, &bodies).map_err(|e| format!("{}: {e}", test.name))?)
    } else {
        return Err(format!(
            "{}: either every thread or none has a code_base",
            test.name
        ));
    };
    let funcs: Vec<Vec<u8>> = if fixed.is_empty() {
        test.threads
            .iter()
            .map(|t| wrap::function(&t.code))
            .collect()
    } else {
        fixed.iter().map(|b| wrap::stub(*b)).collect()
    };
    let (_code, entries) = Mapping::code(&funcs)?;
    let init: Vec<[u64; 16]> = test
        .threads
        .iter()
        .map(|t| {
            let mut r = [0u64; 16];
            for (k, v) in &t.regs {
                r[*k as usize] = *v;
            }
            r
        })
        .collect();
    let slots: Vec<[AtomicU64; 16]> = (0..n)
        .map(|_| std::array::from_fn(|_| AtomicU64::new(0)))
        .collect();
    let barrier = Barrier {
        n,
        count: AtomicUsize::new(0),
        epoch: AtomicUsize::new(0),
    };
    let stop = AtomicBool::new(false);
    let pin_failed = AtomicBool::new(false);
    let base = data.base as usize;
    let reset = || {
        for l in &test.locs {
            let a = base + (l.addr - DATA_BASE) as usize;
            for (i, b) in l.init.iter().enumerate() {
                // SAFETY: inside the data mapping (checked above); no test thread runs now.
                unsafe { std::ptr::write_volatile((a + i) as *mut u8, *b) };
            }
        }
    };
    let read = || -> Vec<Vec<u8>> {
        test.locs
            .iter()
            .map(|l| {
                let a = base + (l.addr - DATA_BASE) as usize;
                (0..l.init.len())
                    // SAFETY: inside the data mapping; all test threads are past the barrier.
                    .map(|i| unsafe { std::ptr::read_volatile((a + i) as *const u8) })
                    .collect()
            })
            .collect()
    };
    let start = Instant::now();
    let result = std::thread::scope(|s| {
        let mut handles = Vec::new();
        for t in 0..n {
            let (barrier, stop, slots, init) = (&barrier, &stop, &slots, &init);
            let pin_failed = &pin_failed;
            let (reset, read) = (&reset, &read);
            let entry = entries[t];
            let cpu = p.cpus[t];
            let mut rng = Rng::new(p.seed, index, t);
            handles.push(s.spawn(move || -> Result<Option<Run>, String> {
                let pinned = pin(cpu);
                if pinned.is_err() {
                    pin_failed.store(true, Ordering::Relaxed);
                }
                barrier.wait();
                // SAFETY: `entry` is the start of `wrap::function` bytes in an RX mapping that
                // outlives this scope; the function follows the System V ABI and its argument
                // points to a 16-word register file.
                let f: extern "C" fn(*mut u64) = unsafe { std::mem::transmute(entry) };
                let mut hist: BTreeMap<Outcome, u64> = BTreeMap::new();
                let mut i = 0u64;
                let mut capped = false;
                loop {
                    if t == 0 {
                        let done_iters = p.iters.is_some_and(|k| i >= k);
                        let done_time = i.is_multiple_of(256) && start.elapsed() >= p.time;
                        if pin_failed.load(Ordering::Relaxed) || done_iters || done_time {
                            capped = done_time && !done_iters && p.iters.is_some();
                            stop.store(true, Ordering::Relaxed);
                        } else {
                            reset();
                        }
                    }
                    barrier.wait();
                    if stop.load(Ordering::Relaxed) {
                        break;
                    }
                    delay(rng.next() % (p.delay + 1));
                    let mut regs = init[t];
                    f(regs.as_mut_ptr());
                    for (slot, v) in slots[t].iter().zip(regs) {
                        slot.store(v, Ordering::Relaxed);
                    }
                    barrier.wait();
                    if t == 0 {
                        let regs = test
                            .threads
                            .iter()
                            .enumerate()
                            .map(|(k, th)| {
                                th.observe
                                    .iter()
                                    .map(|r| slots[k][*r as usize].load(Ordering::Relaxed))
                                    .collect()
                            })
                            .collect();
                        *hist.entry(Outcome { regs, mem: read() }).or_default() += 1;
                        i += 1;
                    }
                }
                pinned?;
                Ok((t == 0).then(|| Run {
                    iterations: i,
                    elapsed: start.elapsed(),
                    capped,
                    hist,
                }))
            }));
        }
        let mut out = None;
        let mut err = None;
        for h in handles {
            match h.join() {
                Ok(Ok(Some(r))) => out = Some(r),
                Ok(Ok(None)) => {}
                Ok(Err(e)) => err = Some(e),
                Err(_) => err = Some("a litmus thread panicked".into()),
            }
        }
        match (err, out) {
            (Some(e), _) => Err(e),
            (None, Some(r)) => Ok(r),
            (None, None) => Err("no result".into()),
        }
    });
    result.map_err(|e| format!("{}: {e}", test.name))
}
