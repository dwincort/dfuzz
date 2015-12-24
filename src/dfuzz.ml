(* Copyright (c) 2013, The Trustees of the University of Pennsylvania
   All rights reserved.

   LICENSE: 3-clause BSD style.
   See the LICENSE file for details on licensing.
*)
open Unix

open Types

open Support.Options
open Support.Error

let infile     = ref ("" : string)

let argDefs = [
  "-v",                Arg.Int  (fun l  -> debug_options := {!debug_options with level = l} ),       "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;
  "--verbose",         Arg.Int  (fun l  -> debug_options := {!debug_options with level = l} ),       "Set printing level to n (1 Warning [2 Info], 3+ Debug)" ;

  "--disable-types",   Arg.Unit (fun () -> comp_disable TypeChecker ), "Disable type checking and inference" ;
  "--disable-interp",  Arg.Unit (fun () -> comp_disable Interpreter ), "Disable interpreter" ;

  "--disable-unicode", Arg.Unit (fun () -> debug_options := {!debug_options with unicode = false} ), "Disable unicode printing" ;
  "--enable-annot",    Arg.Unit (fun () -> debug_options := {!debug_options with pr_ann  = true} ),  "Enable printing of type annotations" ;
  "--print-var-full",  Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarBoth} ), "Print names and indexes of variables" ;
  "--print-var-index", Arg.Unit (fun () -> debug_options := {!debug_options with var_output = PrVarIndex}), "Print just indexes of variables" ;
]

let dp = Support.FileInfo.dummyinfo
let main_error = error_msg General

let main_warning fi = message 1 General fi
let main_info    fi = message 2 General fi
let main_info2   fi = message 3 General fi
let main_debug   fi = message 4 General fi

let parseArgs () =
  let inFile = ref (None : string option) in
  Arg.parse argDefs
     (fun s ->
       match !inFile with
         Some(_) -> main_error dp "You must specify exactly one input file"
       | None -> inFile := Some(s))
     "Usage: fuzz [options] inputfile";
  match !inFile with
      None    -> main_error dp "No input file specified (use --help to display usage info)"; ""
    | Some(s) -> s

(* Parse the input *)
let parse file =
  let readme,writeme = Unix.pipe () in
  ignore (Unix.create_process
      "/usr/bin/cpp" [|"/usr/bin/cpp" ; "-w" ; "-include" ; "lib/primitives.fz" ; file |]
      Unix.stdin writeme Unix.stderr);
  Unix.close writeme;
  let pi = Unix.in_channel_of_descr readme in
  let lexbuf = Lexer.create file pi in
  let program =
    try Parser.body Lexer.main lexbuf
    with Parsing.Parse_error -> error_msg Parser (Lexer.info lexbuf) "Parse error" in
  Parsing.clear_parser();
  close_in pi;
  program

(* Main must be db_source -> fuzzy string *)
let check_main_type ty =
  match ty with
  | TyPrim PrimString -> ()
  | _ -> main_error dp "The type of the program must be string"

let type_check program =
  let ty = Tycheck.get_type false program  in

  main_info  dp "Type of the program: @[%a@]" Print.pp_type ty;
  
  if comp_enabled Interpreter then check_main_type ty else ()  


(* Must use this *)
(* let get_tty_size = () *)

(* === The main function === *)
let main () =

  (* Setup the pretty printing engine *)

  let fmt_margin =
    try
      snd (Util.get_terminal_size ())
    with _ ->
      main_warning dp "Failed to get terminal size value.";
      120
  in

  let set_pp fmt =
    Format.pp_set_ellipsis_text fmt "[...]";
    Format.pp_set_margin fmt (fmt_margin + 1); (* Don't ever ask *)
    Format.pp_set_max_indent fmt fmt_margin    in

  set_pp Format.std_formatter;
  set_pp Format.err_formatter;

  (* Read the command-line arguments *)
  infile  := parseArgs();

  let program    = parse !infile              in

  (* Print the results of the parsing phase *)
  main_debug dp "Parsed program:@\n@[%a@]@." Print.pp_term program;

  if comp_enabled TypeChecker then
    type_check program;

  if comp_enabled Interpreter then
    let outputStr = Interpreter.run_interp program Prim.prim_list in
    main_info dp "The result of the program: %s" outputStr;
  ()

(* === Call the main function and catch any exceptions === *)

let res =
  try main();
      0
  with Exit x -> x
let () = exit res

