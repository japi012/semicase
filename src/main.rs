use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    process::ExitCode,
};

mod interpreter;
mod lexer;
mod parser;

fn main() -> ExitCode {
    let mut args = std::env::args();
    let _program_name = args.next().unwrap();

    if let Some(filename) = args.next() {
        let src = match std::fs::read_to_string(&filename) {
            Ok(src) => src,
            Err(e) => {
                eprintln!("couldn't open file `{filename}`: {e}");
                return ExitCode::FAILURE;
            }
        };
        match interpret(args.collect(), Path::new(&filename), &src) {
            Ok(_) => ExitCode::SUCCESS,
            Err(_) => ExitCode::FAILURE,
        }
    } else {
        eprintln!("provide a filepath as an argument");
        ExitCode::FAILURE
    }
}

fn interpret(args: Vec<String>, path: &Path, src: &str) -> Result<(), ()> {
    use interpreter::Interpreter;
    use parser::Parser;

    let program = Parser::new(path.to_owned(), &src)
        .program()
        .map(|p| {
            p.flatten_includes(
                path.to_owned(),
                path.canonicalize()
                    .unwrap_or_else(|_| panic!("couldn't find absolute path"))
                    .parent()
                    .unwrap_or(Path::new("/")),
                &mut vec![path.to_owned()],
            )
        })
        .map_err(|e| eprintln!("{e:?}"))?
        .map_err(|e| eprintln!("{e:?}"))?;

    let mut interpreter = Interpreter::default();

    let program = program.into_values();
    let mut registered: HashMap<PathBuf, Vec<crate::parser::Def>> = HashMap::new();

    for (path, def) in program {
        if let Some(defs) = registered.get_mut(&path) {
            defs.push(def)
        } else {
            registered.insert(path, vec![def]);
        }
    }

    interpreter.register(registered.into_iter().collect());
    interpreter
        .run(args)
        .map_err(|e| interpreter::report_error(e, &mut std::io::stderr()).unwrap())?;

    Ok(())
}