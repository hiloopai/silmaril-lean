//! `hello`: writes `Hello, WASI 0.3!\n` to stdout through a `stream<u8>`.
#![no_std]

extern crate alloc;
extern crate p3rt;

wasip3::cli::command::export!(Hello);

struct Hello;

impl wasip3::exports::cli::run::Guest for Hello {
    async fn run() -> Result<(),> {
        let (mut tx, rx) = wasip3::wit_stream::new();
        let (written,) = futures::join!(
            async { wasip3::cli::stdout::write_via_stream(rx).await },
            async {
                let rest = tx.write_all(b"Hello, WASI 0.3!\n".to_vec()).await;
                assert!(rest.is_empty());
                drop(tx);
            }
        );
        written.map_err(|_|)
    }
}
