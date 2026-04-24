mod codegen;
mod compiler;
mod cond;
mod expr;
mod math;
mod memstate;
mod nodes;
mod opt;
mod parser;

use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::process;

use compiler::Compiler;

fn usage(progname: &str) {
    eprintln!(
        r#"Esotope Brainfuck compiler
Copyright (c) 2009, Kang Seonghoon.

Usage: {progname} [options] filename  (from file)
       {progname} [options] -         (from stdin)

Options:
-h, --help
    Shows this message.
-i FORMAT, --input-format FORMAT
    Sets the parser module. FORMAT can be "brainfuck" or "bfrle",
    and defaults to the extension supplied.
-f FORMAT, --output-format FORMAT
    Sets the code generator module. FORMAT can be "c", and defaults
    to "c" currently.
-s BITS, --cellsize BITS
    Sets the size of each memory size. BITS can be 8, 16 or 32, and
    defaults to 8.
-v, --verbose
    Prints more internal progress.
--debug
    Enables debugging output (as C comment) in the code.

For more information please visit http://esotope-bfc.googlecode.com/.
"#,
    );
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let progname = &args[0];

    let mut cellsize: u32 = 8;
    let mut informat: Option<String> = None;
    let mut _outformat = "c".to_string();
    let mut _verbose = false;
    let mut debugging = false;
    let mut filename: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                usage(progname);
                process::exit(0);
            }
            "-i" | "--input-format" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -i requires an argument");
                    process::exit(1);
                }
                let fmt = args[i].to_lowercase().trim().to_string();
                if fmt != "brainfuck" && fmt != "bfrle" {
                    eprintln!("Error: Invalid input format {:?}.", args[i]);
                    process::exit(1);
                }
                informat = Some(fmt);
            }
            "-f" | "--output-format" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -f requires an argument");
                    process::exit(1);
                }
                let fmt = args[i].to_lowercase().trim().to_string();
                if fmt != "c" {
                    eprintln!("Error: Invalid output format {:?}.", args[i]);
                    process::exit(1);
                }
                _outformat = fmt;
            }
            "-s" | "--cellsize" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: -s requires an argument");
                    process::exit(1);
                }
                match args[i].parse::<u32>() {
                    Ok(cs) if cs == 8 || cs == 16 || cs == 32 => cellsize = cs,
                    _ => {
                        eprintln!("Error: Invalid cell size {:?}.", args[i]);
                        process::exit(1);
                    }
                }
            }
            "-v" | "--verbose" => {
                _verbose = true;
            }
            "--debug" => {
                debugging = true;
            }
            s if s.starts_with('-') && s.len() > 1 && s != "-" => {
                eprintln!("Error: Unknown option {}.", s);
                eprintln!("Type \"{} --help\" for usage.", progname);
                process::exit(1);
            }
            _ => {
                filename = Some(args[i].clone());
            }
        }
        i += 1;
    }

    let filename = match filename {
        Some(f) => f,
        None => {
            eprintln!("Type \"{} --help\" for usage.", progname);
            process::exit(1);
        }
    };

    let informat = informat.unwrap_or_else(|| {
        if filename.ends_with(".bfrle") {
            "bfrle".to_string()
        } else {
            "brainfuck".to_string()
        }
    });

    let reader: Box<dyn BufRead> = if filename == "-" {
        Box::new(BufReader::new(io::stdin()))
    } else {
        match File::open(&filename) {
            Ok(f) => Box::new(BufReader::new(f)),
            Err(e) => {
                eprintln!("Error: Cannot open {}: {}", filename, e);
                process::exit(1);
            }
        }
    };

    let compiler = Compiler::new(cellsize, debugging);
    let mut stdout = io::stdout().lock();

    match compiler.compile(reader, &mut stdout, &informat) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1);
        }
    }
}
