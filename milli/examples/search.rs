// use crate::allocator::ALLOC;
use std::error::Error;
use std::io::stdin;
use std::time::Instant;

use heed::EnvOpenOptions;
use milli::{DetailedSearchLogger, Index, Search, TermsMatchingStrategy};

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: command line
    let mut args = std::env::args();
    let _ = args.next().unwrap();
    let dataset = args.next().unwrap();

    let mut options = EnvOpenOptions::new();
    options.map_size(100 * 1024 * 1024 * 1024); // 100 GB

    let index = Index::new(options, dataset)?;
    let txn = index.read_txn()?;
    let mut query = String::new();
    while stdin().read_line(&mut query)? > 0 {
        for _ in 0..2 {
            let start = Instant::now();
            let mut s = Search::new(&txn, &index);
            s.query(
                // "which a the releases from poison by the government",
                // "sun flower s are the best",
                query.trim(),
            );
            s.terms_matching_strategy(TermsMatchingStrategy::Last);

            let logger = DetailedSearchLogger::new("log");
            let _docs = //s.execute();
            s.execute_with_logger(logger, |logger, ctx| {
                logger.write_d2_description(ctx);
            })
            .unwrap();

            let elapsed = start.elapsed();
            println!("{}us", elapsed.as_micros());
        }
        query.clear();
    }

    Ok(())
}
