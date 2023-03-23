// use crate::allocator::ALLOC;
use std::error::Error;
use std::io::stdin;
use std::time::Instant;

use heed::EnvOpenOptions;
use milli::{
    execute_search, DefaultSearchLogger, Index, Search, SearchContext, TermsMatchingStrategy,
};

#[global_allocator]
static ALLOC: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), Box<dyn Error>> {
    // TODO: command line
    let mut args = std::env::args();
    let _ = args.next().unwrap();
    let dataset = args.next().unwrap();

    let mut options = EnvOpenOptions::new();
    options.map_size(100 * 1024 * 1024 * 1024); // 100 GB

    // Query:
    // disp: 20
    //
    // dasp: 70 words
    // dosp: 80
    // dasc: 80
    //
    //
    // daspouyerf
    // daspojewkfb

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
            // s.limit(1);
            // s.criterion_implementation_strategy(
            //     milli::CriterionImplementationStrategy::OnlySetBased,
            // );

            let docs = s.execute().unwrap();
            let elapsed = start.elapsed();
            println!("{}us", elapsed.as_micros());

            // let documents = index
            //     .documents(&txn, docs.documents_ids.iter().copied())
            //     .unwrap()
            //     .into_iter()
            //     .map(|(id, obkv)| {
            //         let mut object = serde_json::Map::default();
            //         for (fid, fid_name) in index.fields_ids_map(&txn).unwrap().iter() {
            //             let value = obkv.get(fid).unwrap();
            //             let value: serde_json::Value = serde_json::from_slice(value).unwrap();
            //             object.insert(fid_name.to_owned(), value);
            //         }
            //         (id, serde_json::to_string_pretty(&object).unwrap())
            //     })
            //     .collect::<Vec<_>>();

            // println!("{}us: {:?}", elapsed.as_micros(), docs.documents_ids);
            // for (id, document) in documents {
            //     println!("{id}:");
            //     println!("{document}");
            // }

            // let documents = index
            //     .documents(&txn, docs.documents_ids.iter().copied())
            //     .unwrap()
            //     .into_iter()
            //     .map(|(id, obkv)| {
            //         let mut object = serde_json::Map::default();
            //         for (fid, fid_name) in index.fields_ids_map(&txn).unwrap().iter() {
            //             let value = obkv.get(fid).unwrap();
            //             let value: serde_json::Value = serde_json::from_slice(value).unwrap();
            //             object.insert(fid_name.to_owned(), value);
            //         }
            //         (id, serde_json::to_string_pretty(&object).unwrap())
            //     })
            //     .collect::<Vec<_>>();
            // println!("{}us: {:?}", elapsed.as_micros(), docs.documents_ids);
            // for (id, document) in documents {
            //     println!("{id}:");
            //     println!("{document}");
            // }
        }
        query.clear();
    }
    // for (id, document) in documents {
    //     println!("{id}:");
    //     // println!("{document}");
    // }

    Ok(())
}
