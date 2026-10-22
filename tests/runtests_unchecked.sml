open HolKernel GetOpt vfmTestAuxLib vfmTestLib

val usage_header = String.concat [
  "runtests_unchecked.exe [options] [<num> ...]\n",
  "Run EEST fixtures using EmitML-generated code.\n",
  "Run from tests/. Results are written to results/.\n",
  "With no indices, run serial-first.txt fixtures first, then the rest.\n"
]

datatype options = Help | Results | NoResults | Fresh | NoSerialFirst
                 | Limit of string | GasRate of string | Jobs of string
                 | Table of string

(* Half the slowest rate GitHub's runners showed on a heavy case; see
   tests/README.md. *)
val default_gas_rate = 350000

val cline_options = [
  {short="h", long=["help"], desc=NoArg (K Help), help="only print help"},
  {short="r", long=["results"], desc=NoArg (K Results),
   help="only write results table"},
  {short="n", long=["noresults"], desc=NoArg (K NoResults),
   help="do not write the results table"},
  {short="f", long=["fresh"], desc=NoArg (K Fresh),
   help="rerun selected cases instead of resuming"},
  {short="", long=["no-serial-first"], desc=NoArg (K NoSerialFirst),
   help="schedule all fixtures together"},
  {short="t", long=["time"], desc=ReqArg (Limit, "secs"),
   help="minimum time limit per case, including input encoding (default: VFM_TIME_LIMIT or 60)"},
  {short="", long=["gas-rate"], desc=ReqArg (GasRate, "gas"),
   help=String.concat ["raise a case's time limit to its gas divided by this ",
                       "many gas per second; 0 turns this off (default: ",
                       Int.toString default_gas_rate, ")"]},
  {short="j", long=["jobs"], desc=ReqArg (Jobs, "num"),
   help="number of fixture worker processes (default: 1)"},
  {short="", long=["table"], desc=ReqArg (Table, "file"),
   help="name of the results table in results/ (default: table.html)"}
]

val usage = usageInfo {header=usage_header, options=cline_options}
fun err s = TextIO.output(TextIO.stdErr, s)
fun die s = (err s; OS.Process.exit OS.Process.failure)

fun read_text path = let
  val input = TextIO.openIn path
in TextIO.inputAll input before TextIO.closeIn input end

fun write_text path text = let
  val output = TextIO.openOut path
in TextIO.output(output, text) before TextIO.closeOut output end

fun read_serial_first () = let
  val trim = Substring.string o Substring.dropl Char.isSpace o
             Substring.dropr Char.isSpace o Substring.full
in
  List.filter (fn s => s <> "" andalso not (String.isPrefix "#" s))
    (List.map trim (String.fields (equal #"\n")
      (read_text (test_path "serial-first.txt"))))
end

fun positive_integer label s =
  if s <> "" andalso List.all Char.isDigit (String.explode s)
  then case Int.fromString s of
      SOME n => if n > 0 then n else raise Fail (label ^ " must be positive")
    | NONE => raise Fail ("invalid " ^ label ^ ": " ^ s)
  else raise Fail ("invalid " ^ label ^ ": " ^ s)

fun selected_fixtures paths indices = let
  val all = Vector.fromList paths
  fun fixture s =
    if s <> "" andalso List.all Char.isDigit (String.explode s)
    then case Int.fromString s of
        SOME n => if n < Vector.length all
          then (padl 4 #"0" (Int.toString n), Vector.sub(all, n))
          else raise Fail ("fixture index out of range: " ^ s)
      | NONE => raise Fail ("invalid fixture index: " ^ s)
    else raise Fail ("invalid fixture index: " ^ s)
  val selected = if List.null indices
    then List.tabulate(Vector.length all, fn n => fixture (Int.toString n))
    else List.map fixture indices
in
  (* Never let duplicate indices write the same result concurrently. *)
  List.rev (List.foldl (fn (x, xs) => if List.exists (equal x) xs
                                      then xs else x::xs) [] selected)
end

(* A case using much gas gets more time than the minimum limit, so heavy but
   correct cases finish, while a slow case with little gas still times out. *)
fun case_limit limit gas_rate gas =
  if gas_rate = 0 then limit
  else let
    val scaled = Time.fromSeconds (Arbnum.toLargeInt gas div Int.toLarge gas_rate)
  in
    if Time.>(scaled, limit) then scaled else limit
  end

fun run_fixture fresh limit gas_rate (index, path) = let
  val cases = vfmUncheckedFixtureLib.json_path_to_tests (fixtures_path path)
  val newest_input = List.foldl
    (fn (t, latest) => if Time.>(t, latest) then t else latest)
    Time.zeroTime (List.map OS.FileSys.modTime
      [CommandLine.name (), fixtures_path path, fixtures_path "version.txt"])
  fun run_case (number, {name, gas, evaluate}) = let
    val suffix = index ^ "_" ^ Int.toString number
    val limit_used = case_limit limit gas_rate gas
    val file = results_path ("result" ^ suffix ^ ".nsv")
  in
    if not fresh andalso
       (Time.>=(OS.FileSys.modTime file, newest_input) handle OS.SysErr _ => false)
    then ()
    else let
      val () = if (OS.FileSys.access (file, [OS.FileSys.A_READ])
                   handle OS.SysErr _ => false)
               then OS.FileSys.remove file else ()
      val start = Time.now ()
      val result = Timeout.apply limit_used evaluate ()
                   handle Timeout.TIMEOUT _ => "Timeout"
      val seconds = Time.fmt 2 (Time.now () - start)
      val temporary = file ^ ".tmp"
      val () = write_text temporary
        (String.concatWith "\n" [name, result, seconds, "unchecked"] ^ "\n")
      val () = OS.FileSys.rename {old=temporary, new=file}
    in
      TextIO.print ("test_" ^ suffix ^ "_result = " ^ result ^ " (" ^ seconds ^
                    (if Time.>(limit_used, limit)
                     then "s, limit " ^ Time.fmt 0 limit_used ^ "s)\n"
                     else "s)\n"))
    end
  end
in
  List.app run_case (ListPair.zip (List.tabulate(List.length cases, I), cases))
end

(* Poly/ML disables threads after fork.  Exec a fresh runtime before starting
   the per-case timer; each process still owns exactly one fixture.
   Poly/ML 5.9.2's parallel GC can fail a multi-MB allocation while the heap
   is still small (seen parsing a 25 MB fixture), so workers collect with one
   GC thread.  The RTS removes --gcthreads from the arguments main sees. *)
fun run_workers jobs fresh limit gas_rate fixtures = let
  val executable = OS.FileSys.fullPath (CommandLine.name ())
  val active = ref ([] : Posix.Process.pid list)
  fun spawn (index, path) = let
    val () = TextIO.flushOut TextIO.stdOut
    val () = TextIO.flushOut TextIO.stdErr
  in
    case Posix.Process.fork () of
      SOME pid => active := pid :: !active
    | NONE =>
        (Posix.Process.exec (executable,
           [executable, "--gcthreads", "1", "--worker", Bool.toString fresh,
            Time.toString limit, Int.toString gas_rate, index, path])
         handle _ => Posix.Process.exit 0w1)
  end
  fun reap () = let
    val (pid, status) = Posix.Process.waitpid (Posix.Process.W_ANY_CHILD, [])
    val () = active := List.filter (fn p => p <> pid) (!active)
  in
    case status of Posix.Process.W_EXITED => true | _ => false
  end
  fun loop pending success =
    case pending of
      fixture::rest =>
        if List.length (!active) < jobs
        then (spawn fixture; loop rest success)
        else let val ok = reap () in loop pending (ok andalso success) end
    | [] => if List.null (!active) then success
            else let val ok = reap () in loop [] (ok andalso success) end
  fun stop () =
    (List.app (fn pid =>
       (Posix.Process.kill (Posix.Process.K_PROC pid, Posix.Signal.term)
        handle OS.SysErr _ => ())) (!active);
     while not (List.null (!active)) do ignore (reap ()))
in
  loop fixtures true handle e => (stop (); raise e)
end

fun run options indices = let
  val fresh = List.exists (equal Fresh) options
  val jobs = case List.mapPartial (fn Jobs s => SOME s | _ => NONE) options of
      [] => 1 | s::_ => positive_integer "worker count" s
  val limit = case List.mapPartial (fn Limit s => SOME s | _ => NONE) options of
      [] => Option.getOpt
        (Option.mapPartial Time.fromString (OS.Process.getEnv "VFM_TIME_LIMIT"),
         Time.fromSeconds 60)
    | s::_ => Time.fromSeconds (Int.toLarge (positive_integer "time limit" s))
  val () = if Time.>(limit, Time.zeroTime) then ()
           else raise Fail "time limit must be positive"
  val gas_rate =
    case List.mapPartial (fn GasRate s => SOME s | _ => NONE) options of
      [] => default_gas_rate
    | "0"::_ => 0
    | s::_ => positive_integer "gas rate" s
  val () = ensure_fixtures ()
  val fixtures = selected_fixtures (get_all_test_json_paths ()) indices
  val (serial, rest) =
    if not (List.null indices) orelse List.exists (equal NoSerialFirst) options
    then ([], fixtures)
    else let
      val serial_indices = test_indices (read_serial_first ())
      fun heavy (index, _) = List.exists (equal index) serial_indices
    in (List.filter heavy fixtures, List.filter (not o heavy) fixtures) end
in
  if run_workers 1 fresh limit gas_rate serial
  then run_workers jobs fresh limit gas_rate rest
  else false
end

fun main_cli arguments = let
  val errors = ref ([] : string list)
  val (options, indices) = GetOpt.getOpt
    {argOrder=Permute, options=cline_options,
     errFn=fn s => errors := s :: !errors} arguments
  val () = if List.null (!errors) then ()
           else raise Fail (String.concat (List.rev (!errors)))
  val () = if #file (OS.Path.splitDirFile (OS.FileSys.getDir ())) = "tests"
           then () else raise Fail "must be run from the tests directory"
in
  if List.exists (equal Help) options then TextIO.print usage
  else let
    val table = case List.mapPartial (fn Table s => SOME s | _ => NONE) options of
        [] => "table.html" | s::_ => s
    val success = List.exists (equal Results) options orelse run options indices
    val () = if List.exists (equal NoResults) options then ()
             else (write_test_results_table table;
                   TextIO.print ("Results written to results/" ^ table ^ "\n"))
  in
    if success then () else raise Fail "one or more fixture workers failed"
  end
end

fun main () =
  (case CommandLine.arguments () of
     ["--worker", fresh, seconds, gas_rate, index, path] =>
       (run_fixture (fresh = "true") (Option.valOf (Time.fromString seconds))
          (Option.valOf (Int.fromString gas_rate)) (index, path)
        handle e => raise Fail (index ^ ": " ^ General.exnMessage e))
   | arguments => main_cli arguments)
  handle e => die ("runtests_unchecked.exe: " ^ General.exnMessage e ^ "\n")
