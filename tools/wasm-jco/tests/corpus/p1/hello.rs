// kind: command
// A WASI preview 1 command: arguments, environment, stdin, stdout, stderr, clocks, exit status.
use std::io::Read;
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    println!("args: {:?}", args);
    for (k, v) in std::env::vars() {
        if k.starts_with("SIL") { println!("env {k}={v}"); }
    }
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    eprintln!("stdin: {} bytes, {} lines", s.len(), s.lines().count());
    let words: usize = s.split_whitespace().count();
    println!("words: {words}");
    let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap();
    println!("clock: {}", if t.as_secs() > 1_000_000_000 { "after 2001" } else { "early" });
    let i = std::time::Instant::now();
    let _ = i.elapsed();
    if s.contains("fail") { std::process::exit(3); }
}
