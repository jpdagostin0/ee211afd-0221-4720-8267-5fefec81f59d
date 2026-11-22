mod generic;
mod pqw;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (data, out): (String, String) = if args.len() >= 3 {
        (args[args.len() - 2].clone(), args[args.len() - 1].clone())
    } else {
        (std::env::var("DATA_DIR").unwrap_or_else(|_| "/data".into()), std::env::var("OUTPUT_DIR").unwrap_or_else(|_| "/output".into()))
    };
    let ncpu: usize = std::env::var("NCPU").ok().and_then(|s| s.trim().parse().ok()).filter(|&n| n > 0).unwrap_or(8);
    if let Err(e) = generic::run(std::path::Path::new(&data), std::path::Path::new(&out), ncpu) {
        eprintln!("error: {e}");
        std::process::exit(1);
    }
}
