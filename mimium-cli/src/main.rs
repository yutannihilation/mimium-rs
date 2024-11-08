use std::io::stdin;
use std::path::{Path, PathBuf};

// pub mod wcalculus;
use clap::{Parser, ValueEnum};
use mimium_audiodriver::backends::csv::{csv_driver, csv_driver_stdout};
use mimium_audiodriver::driver::{load_default_runtime, SampleRate};
use mimium_lang::compiler::emit_ast;
use mimium_lang::interner::{ExprNodeId, Symbol, ToSymbol};
use mimium_lang::log;
use mimium_lang::plugin::Plugin;
use mimium_lang::utils::error::ReportableError;
use mimium_lang::utils::miniprint::MiniPrint;
use mimium_lang::utils::{error::report, fileloader};
use mimium_lang::ExecContext;
use mimium_lang::{compiler::mirgen::convert_pronoun, repl};
use mimium_midi;
use mimium_symphonia::{self, SamplerPlugin};
#[derive(clap::Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    #[command(flatten)]
    pub mode: Mode,

    /// File name
    #[clap(value_parser)]
    pub file: Option<String>,

    /// Write out the signal values to a file (e.g. out.csv).
    #[arg(long, short)]
    pub output: Option<PathBuf>,

    /// Output format
    #[arg(long, value_enum)]
    pub output_format: Option<OutputFileFormat>,

    /// How many times to execute the code. This is only effective when --output
    /// is specified.
    #[arg(long, default_value_t = 10)]
    pub times: usize,
}

#[derive(Clone, Debug, ValueEnum)]
pub enum OutputFileFormat {
    Csv,
}

#[derive(clap::Args, Debug)]
#[group(required = false, multiple = false)]
pub struct Mode {
    /// Print AST and exit
    #[arg(long, default_value_t = false)]
    pub emit_ast: bool,

    /// Print MIR and exit
    #[arg(long, default_value_t = false)]
    pub emit_mir: bool,

    /// Print bytecode and exit
    #[arg(long, default_value_t = false)]
    pub emit_bytecode: bool,
}

fn emit_ast_local(src: &str, filepath: &Path) -> Result<ExprNodeId, Vec<Box<dyn ReportableError>>> {
    let ast1 = emit_ast(src, Some(filepath.to_str().unwrap().to_symbol()))?;

    convert_pronoun::convert_pronoun(ast1).map_err(|e| {
        let eb: Vec<Box<dyn ReportableError>> = vec![Box::new(e)];
        eb
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if cfg!(debug_assertions) | cfg!(test) {
        colog::default_builder()
            .filter_level(log::LevelFilter::Debug)
            .init();
    } else {
        colog::default_builder().init();
    }

    let args = Args::parse();
    match &args.file {
        Some(file) => {
            let fullpath = fileloader::get_canonical_path(".", &file)?;
            let content = fileloader::load(fullpath.to_str().unwrap())?;
            match run_file(&args, &content, &fullpath) {
                Ok(_) => {}
                Err(e) => {
                    // Note: I was hoping to implement std::error::Error for a
                    // struct around ReportableError and directly return it,
                    // however, std::error::Error cannot be so color-rich as
                    // ariadne because it just uses std::fmt::Display.
                    report(&content, fullpath, &e);
                    return Err(format!("Failed to process {file}").into());
                }
            }
        }
        None => {
            repl::run_repl();
        }
    }
    Ok(())
}

fn get_default_context(path: Option<Symbol>) -> ExecContext {
    let plugins: Vec<Box<dyn Plugin>> = vec![Box::new(SamplerPlugin)];
    let mut ctx = ExecContext::new(plugins.into_iter(), path);
    ctx.add_system_plugin(mimium_scheduler::get_default_scheduler_plugin());
    ctx.add_system_plugin(mimium_midi::MidiPlugin::default());
    #[cfg(not(target_arch = "wasm32"))]
    ctx.add_system_plugin(mimium_guitools::GuiToolPlugin::default());

    ctx
}

fn run_file(
    args: &Args,
    content: &str,
    fullpath: &Path,
) -> Result<(), Vec<Box<dyn ReportableError>>> {
    log::debug!("Filename: {}", fullpath.display());
    let path_sym = fullpath.to_string_lossy().to_symbol();
    let mut ctx = get_default_context(Some(path_sym));
    if args.mode.emit_ast {
        let ast = emit_ast_local(content, fullpath)?;
        println!("{}", ast.pretty_print());
    } else if args.mode.emit_mir {
        ctx.prepare_compiler();
        let mir = ctx.compiler.as_ref().unwrap().emit_mir(content)?;
        println!("{mir}");
    } else {
        ctx.prepare_machine(content)?;

        if args.mode.emit_bytecode {
            println!("{}", ctx.vm.unwrap().prog);
            return Ok(());
        }

        let mut driver = match (&args.output_format, &args.output) {
            // if none of the output options is specified, make sounds.
            (None, None) => load_default_runtime(),
            // When --output-format is explicitly specified, use it.
            (Some(OutputFileFormat::Csv), Some(output)) => csv_driver(args.times, output),
            (Some(OutputFileFormat::Csv), None) => csv_driver_stdout(args.times),
            // Otherwise, guess from the file extension.
            (None, Some(output)) => match output.extension() {
                Some(x) if &x.to_os_string() == "csv" => csv_driver(args.times, output),
                _ => panic!("cannot determine the output file format"),
            },
        };
        let audiodriver_plug = driver.get_as_plugin();
        ctx.add_plugin(audiodriver_plug);
        let _res = ctx.run_main();
        let mainloop = ctx.try_get_main_loop().unwrap_or(Box::new(|| {
            //wait until input something
            let mut dummy = String::new();
            eprintln!("Press Enter to exit");
            let _size = stdin().read_line(&mut dummy).expect("stdin read error.");
        }));
        driver.init(ctx, Some(SampleRate(48000)));
        driver.play();
        mainloop()
    }

    Ok(())
}
