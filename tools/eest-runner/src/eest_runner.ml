(* Runs the software guest on one framed EEST input with the extracted
   [Runner.runInput], with spike_run's command line: [ELF] INPUT OUTPUT.
   The ELF argument is ignored.  The input file is an 8-byte little-endian
   length followed by the payload; OUTPUT receives SPIKE_OUTPUT_LEN output
   bytes (default 256).  EEST_RUNNER_CLOCK sets the source clock. *)
open Runner_extracted

let env_int name default =
  match Sys.getenv_opt name with
  | None | Some "" -> default
  | Some s -> (try int_of_string s with _ -> Printf.eprintf "bad %s=%s\n" name s; exit 2)

let read_input path =
  let ic = open_in_bin path in
  let data = really_input_string ic (in_channel_length ic) in
  close_in ic;
  if String.length data < 8 then (Printf.eprintf "input shorter than 8 bytes\n"; exit 2);
  let len = Int64.to_int (String.get_int64_le data 0) in
  if len < 0 || 8 + len > String.length data then
    (Printf.eprintf "input length %d exceeds file\n" len; exit 2);
  List.init len (fun i -> Z.of_int (Char.code data.[8 + i]))

let bytes_of words =
  String.of_seq (Seq.map (fun w -> Char.chr (Z.to_int w)) (List.to_seq words))

let () =
  let input_path, output_path =
    match Array.to_list Sys.argv with
    | [_; _; i; o] | [_; i; o] -> i, o
    | _ -> prerr_endline "usage: eest_runner [ELF] INPUT OUTPUT"; exit 2 in
  let len = env_int "SPIKE_OUTPUT_LEN" 256 in
  let clock = env_int "EEST_RUNNER_CLOCK" (1 lsl 40) in
  let input = read_input input_path in
  let t0 = Unix.gettimeofday () in
  let r = runInput (Z.of_int clock) len input in
  let secs = Unix.gettimeofday () -. t0 in
  let oc = open_out_bin output_path in
  output_string oc (bytes_of r.output);
  close_out oc;
  let stats = Printf.sprintf "clock=%s events=%s secs=%.3f"
      (Z.to_string r.clockUsed) (Z.to_string r.eventCount) secs in
  match r.outcome with
  | Halted (_, _) -> Printf.eprintf "eest_runner: halted %s\n" stats; exit 0
  | Trapped c ->
    Printf.eprintf "eest_runner: trap [%s] %s\n"
      (String.concat ";" (List.map Z.to_string c)) stats; exit 3
  | TimedOut -> Printf.eprintf "eest_runner: clock exhausted %s\n" stats; exit 4
  | Failed -> Printf.eprintf "eest_runner: error %s\n" stats; exit 5
  | OtherFinal _ -> Printf.eprintf "eest_runner: other final call %s\n" stats; exit 6
