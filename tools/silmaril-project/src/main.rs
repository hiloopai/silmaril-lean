//! `silmaril-project`, run as `sil project …`: silmaril projects (init, artifacts, lock, lint,
//! dump, check, sqlite, explore, schema). The guide is `docs/projects/silmaril-projects.md`.

use clap::Parser;

mod project;

#[derive(Parser)]
#[command(
    name = "sil project",
    bin_name = "sil project",
    version,
    about = "Silmaril projects: declare artifacts, values, problems and their DAG; dump, check and explore them",
    long_about = None
)]
struct Cli {
    #[command(subcommand)]
    command: project::Command,
}

fn main() -> miette::Result<()> {
    project::run(Cli::parse().command)
}
