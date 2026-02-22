use std::env;
use std::process;
use umark_lib::{MarkdownFlavor, parse_from_file_with_flavor, safe_parse_from_file_with_flavor};

fn print_usage(program: &str) {
    eprintln!(
        "Usage: {program} <input.md> <output.html> [--flavor gfm|commonmark] [--safe]\n\
         \n\
         Options:\n\
         --flavor <name>   Markdown flavor to use (default: gfm)\n\
         --safe            Reject raw HTML and script tags\n\
         -h, --help        Show this help message"
    );
}

fn parse_flavor(value: &str) -> Option<MarkdownFlavor> {
    if value.eq_ignore_ascii_case("gfm") {
        Some(MarkdownFlavor::Gfm)
    } else if value.eq_ignore_ascii_case("commonmark") {
        Some(MarkdownFlavor::CommonMark)
    } else {
        None
    }
}

fn main() {
    let program = env::args().next().unwrap_or_else(|| "umark".to_string());
    let mut args = env::args().skip(1);

    let mut input: Option<String> = None;
    let mut output: Option<String> = None;
    let mut flavor = MarkdownFlavor::Gfm;
    let mut safe_mode = false;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-h" | "--help" => {
                print_usage(&program);
                return;
            }
            "--safe" => safe_mode = true,
            "--flavor" => {
                let Some(value) = args.next() else {
                    eprintln!("error: --flavor requires a value");
                    print_usage(&program);
                    process::exit(2);
                };
                let Some(parsed) = parse_flavor(&value) else {
                    eprintln!("error: unknown flavor '{value}'");
                    print_usage(&program);
                    process::exit(2);
                };
                flavor = parsed;
            }
            _ => {
                if let Some(value) = arg.strip_prefix("--flavor=") {
                    let Some(parsed) = parse_flavor(value) else {
                        eprintln!("error: unknown flavor '{value}'");
                        print_usage(&program);
                        process::exit(2);
                    };
                    flavor = parsed;
                } else if input.is_none() {
                    input = Some(arg);
                } else if output.is_none() {
                    output = Some(arg);
                } else {
                    eprintln!("error: unexpected argument '{arg}'");
                    print_usage(&program);
                    process::exit(2);
                }
            }
        }
    }

    let (Some(input_path), Some(output_path)) = (input, output) else {
        print_usage(&program);
        process::exit(2);
    };

    let result = if safe_mode {
        safe_parse_from_file_with_flavor(&input_path, &output_path, flavor)
    } else {
        parse_from_file_with_flavor(&input_path, &output_path, flavor)
    };

    if let Err(err) = result {
        eprintln!("error: {err}");
        process::exit(1);
    }
}
