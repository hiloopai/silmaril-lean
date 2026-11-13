// kind: command
// A WASI preview 1 command using the file system: the preopened directory /sandbox.
use std::io::Write;
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = args.first().and_then(|a| a.parse().ok()).unwrap_or(3);
    let path = "/sandbox/sil-p1.txt";
    {
        let mut f = std::fs::File::create(path).expect("create");
        for i in 0..n { writeln!(f, "line {i}: {}", "x".repeat(i)).unwrap(); }
    }
    let text = std::fs::read_to_string(path).expect("read");
    println!("read back {} bytes, {} lines", text.len(), text.lines().count());
    let meta = std::fs::metadata(path).expect("metadata");
    println!("size {} file {}", meta.len(), meta.is_file());
    let mut names: Vec<String> = std::fs::read_dir("/sandbox").expect("read_dir")
        .filter_map(|e| e.ok()).map(|e| e.file_name().to_string_lossy().into_owned())
        .filter(|n| n.starts_with("sil-p1")).collect();
    names.sort();
    println!("entries {:?}", names);
    std::fs::remove_file(path).expect("remove");
    println!("removed: {}", std::fs::metadata(path).is_err());
    match std::fs::read_to_string("/sandbox/does-not-exist") {
        Ok(_) => println!("unexpected"),
        Err(e) => println!("missing file: {:?}", e.kind()),
    }
}
