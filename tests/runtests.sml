open HolKernel GetOpt vfmTestLib

val usage_header = String.concat [
  "runtests.exe [options] [<num> ...]\n",
  "Run Verifereum on the EEST suite. If numbers are provided,\n",
  "only run those tests, otherwise run all tests, building the tests\n",
  "listed in serial-first.txt one at a time first. Options:"
]

fun err s = TextIO.output(TextIO.stdErr, s)

datatype options = Help | Results | NoResults | Generate | Fresh
                 | NoSerialFirst
                 | Option of string | Limit of string | Backend of string
fun destOption (Option s) = SOME s | destOption _ = NONE
fun destLimit (Limit s) = SOME s | destLimit _ = NONE
fun destBackend (Backend s) = SOME s | destBackend _ = NONE

val cline_options = [
  {short = "h",
   long = ["help"],
   desc = NoArg (K Help),
   help = "only print help"},
  {short = "r",
   long = ["results"],
   desc = NoArg (K Results),
   help = "only write results table"},
  {short = "g",
   long = ["generate"],
   desc = NoArg (K Generate),
   help = "only generate script files"},
  {short = "n",
   long = ["noresults"],
   desc = NoArg (K NoResults),
   help = "do not write results table"},
  {short = "f",
   long = ["fresh"],
   desc = NoArg (K Fresh),
   help = "rerun selected tests instead of resuming"},
  {short = "",
   long = ["no-serial-first"],
   desc = NoArg (K NoSerialFirst),
   help = "do not build the tests in serial-first.txt first"},
  {short = "t",
   long = ["time"],
   desc = ReqArg (Limit, "secs"),
   help = "override time limit per test"},
  {short = "o",
   long = ["option"],
   desc = ReqArg (Option, "opt"),
   help = "pass an additional option to the selected build backend"},
  {short = "b",
   long = ["backend"],
   desc = ReqArg (Backend, "holbuild|holmake"),
   help = "select build backend (default: holbuild)"}
]
val cline_config = {
  argOrder = Permute,
  options = cline_options,
  errFn = err
}
val usage = usageInfo {header=usage_header, options=cline_options}

fun die s = err s before OS.Process.exit OS.Process.failure

fun thyn i = String.concat ["vfmTest", i, "Theory"]
fun command_arg s = " " ^ s

val bare_Holmake = OS.Path.concat(
  OS.Path.concat(Globals.HOLDIR, "bin"), "Holmake")

fun executable path =
  OS.FileSys.access(path, [OS.FileSys.A_EXEC]) handle OS.SysErr _ => false

fun command_available command =
  OS.Process.isSuccess $ OS.Process.system $
    String.concat ["command -v ", command, " >/dev/null 2>&1"]

fun all_result_targets () =
  List.map (fn script =>
    vfmTestAuxLib.trimr (String.size "Script.sml") script ^ "Theory") $
  collect_script_files "."

fun time_limit_env NONE = ""
  | time_limit_env (SOME s) = "VFM_TIME_LIMIT=" ^ s ^ " "

fun run_holmake fresh limit options indices = let
  val () = if executable bare_Holmake then ()
           else raise Fail $ "selected backend is unavailable: " ^ bare_Holmake
  val options = String.concat (List.map command_arg options)
  val targets = String.concat (List.map (command_arg o thyn) indices)
  val () = if fresh
           then ignore $ OS.Process.system $ String.concat [bare_Holmake, " clean"]
           else ()
in
  OS.Process.system $ String.concat [time_limit_env limit, bare_Holmake,
    " --keep-going", options, targets]
end

fun read_serial_first () = let
  val inp = TextIO.openIn $ vfmTestAuxLib.test_path "serial-first.txt"
  val lines = String.fields (equal #"\n") (TextIO.inputAll inp)
  val () = TextIO.closeIn inp
  val trim = Substring.string o Substring.dropl Char.isSpace o
             Substring.dropr Char.isSpace o Substring.full
in
  List.filter (fn l => l <> "" andalso not (String.isPrefix "#" l)) $
  List.map trim lines
end

fun holbuild_targets fresh limit options targets = let
  val options = String.concat (List.map command_arg options)
  val targets = String.concat (List.map command_arg targets)
  val force = if fresh then " --force=theory" else ""
in
  OS.Process.system $ String.concat [time_limit_env limit,
    "holbuild build --no-cache --skip-proof-steps --skip-checkpoints",
    force, options, targets]
end

(* Building the memory-heavy tests in parallel with others can run out of
   memory, so by default they are built one at a time before the rest. *)
fun run_holbuild serial_first fresh limit options indices = let
  val () = if command_available "holbuild" then ()
           else raise Fail "selected backend is unavailable: holbuild"
  val build = holbuild_targets fresh limit
in
  if not (List.null indices) then build options (List.map thyn indices)
  else if not serial_first then build options (all_result_targets ())
  else let
    val serial = test_indices (read_serial_first ())
    val serial_targets = List.map thyn serial
    val rest = List.filter (fn t => not (mem t serial_targets))
                 (all_result_targets ())
    val st = if List.null serial then OS.Process.success
             else (TextIO.print $ String.concat [
                     "Building serial-first tests one at a time:",
                     String.concat (List.map command_arg serial), "\n"];
                   build (options @ ["-j1"]) serial_targets)
  in
    if OS.Process.isSuccess st then build options rest else st
  end
end

fun run backend serial_first fresh limit options indices = let
  val () = ensure_fixtures ()
  val () = OS.FileSys.chDir "results"
  val st = case backend of
             "holbuild" =>
               run_holbuild serial_first fresh limit options indices
           | "holmake" => run_holmake fresh limit options indices
           | _ => raise Fail $ "unknown backend: " ^ backend
  val () = OS.FileSys.chDir OS.Path.parentArc
in st end

fun main () = let
  val (options, indices) = GetOpt.getOpt cline_config $ CommandLine.arguments()
  val curd = OS.FileSys.getDir()
in
  if (not o equal "tests") $ #file $ OS.Path.splitDirFile $ OS.FileSys.getDir()
  then die "runtests.exe: error: must be run from the tests directory\n"
  else if List.exists (equal Help) options
  then TextIO.print usage
  else if List.exists (equal Generate) options
  then let
         val () = ensure_fixtures ()
         val old = List.map vfmTestAuxLib.defs_path $
                   collect_script_files (vfmTestAuxLib.defs_path "")
         val () = List.app OS.FileSys.remove old
         val () = generate_test_defs_scripts ()
         val () = TextIO.print "Generated scripts in defs\n"
         val old = List.map vfmTestAuxLib.results_path $
                   collect_script_files (vfmTestAuxLib.results_path "")
         val () = List.app OS.FileSys.remove old
         val () = generate_test_results_scripts ()
         val () = TextIO.print "Generated scripts in results\n"
       in () end
  else let
    val backend = case List.mapPartial destBackend options of
                    [] => "holbuild"
                  | backend::_ => backend
    val st = if List.exists (equal Results) options
             then OS.Process.success
             else run backend
               (not (List.exists (equal NoSerialFirst) options))
               (List.exists (equal Fresh) options)
               (List.find (fn _ => true) (List.mapPartial destLimit options))
               (List.mapPartial destOption options)
               indices
  in
    if OS.Process.isSuccess st
    then if List.exists (equal NoResults) options
         then ()
         else write_test_results_table () before
              TextIO.print "Results written to results/table.html\n"
    else die $ "runtests.exe: " ^ backend ^ " failed\n"
  end
end handle e => die $ String.concat [exnName e, ": ", exnMessage e, "\n"]
