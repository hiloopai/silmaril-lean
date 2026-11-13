//! `echo`: writes its arguments (after the program name), separated by spaces and followed
//! by a newline, to stdout.
#![no_std]

extern crate alloc;
extern crate p3rt;

use alloc::vec::Vec;

wasip3::cli::command::export!(Echo);

struct Echo;

impl wasip3::exports::cli::run::Guest for Echo {
    async fn run() -> Result<(),> {
        let args = wasip3::cli::environment::get_arguments();
        let mut line = args.iter().skip(1).cloned().collect::<Vec<_>>().join(" ");
        line.push('\n');
        let (mut tx, rx) = wasip3::wit_stream::new();
        let (written,) = futures::join!(
            async { wasip3::cli::stdout::write_via_stream(rx).await },
            async {
                let rest = tx.write_all(line.into_bytes()).await;
                assert!(rest.is_empty());
                drop(tx);
            }
        );
        written.map_err(|_|)
    }
}
