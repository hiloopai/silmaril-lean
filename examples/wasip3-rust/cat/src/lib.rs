//! `cat`: copies stdin to stdout, one chunk of at most 4096 bytes at a time, through the
//! guest (it reads from the stdin stream and writes each chunk to a stream it gave stdout).
#![no_std]

extern crate alloc;
extern crate p3rt;

use alloc::vec::Vec;

wasip3::cli::command::export!(Cat);

struct Cat;

impl wasip3::exports::cli::run::Guest for Cat {
    async fn run() -> Result<(),> {
        let (mut input, input_done) = wasip3::cli::stdin::read_via_stream();
        let (mut tx, rx) = wasip3::wit_stream::new();
        let (written, ok) = futures::join!(
            async { wasip3::cli::stdout::write_via_stream(rx).await },
            async {
                loop {
                    let (status, chunk) = input.read(Vec::with_capacity(4096)).await;
                    if !chunk.is_empty() {
                        let rest = tx.write_all(chunk).await;
                        if !rest.is_empty() {
                            return false;
                        }
                    }
                    if let wasip3::wit_bindgen::StreamResult::Complete(_) = status {
                        continue;
                    }
                    break;
                }
                drop(tx);
                input_done.await.is_ok()
            }
        );
        if ok { written.map_err(|_|) } else { Err(()) }
    }
}
