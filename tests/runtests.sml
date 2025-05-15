open HolKernel GetOpt vfmTestLib

val usage_header = String.concat [
  "runtests.exe [<num> ...]\n",
  "Run Verifereum on the EEST suite. If numbers are provided,\n",
  "only run those tests, otherwise run all tests."
]

fun err s = TextIO.output(TextIO.stdErr, s)

datatype options = Help | Results | NoResults | Generate | Option of string
fun destOption (Option s) = SOME s | destOption _ = NONE

val cline_options = [
  {short = "h",
   long = ["help"],
   desc = NoArg (K Help),
   help = "print help"},
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
  {short = "o",
   long = ["option"],
   desc = ReqArg (Option, "opt"),
   help = "pass an additional option to Holmake"}
]
val cline_config = {
  argOrder = Permute,
  options = cline_options,
  errFn = err
}
val usage = usageInfo {header=usage_header, options=cline_options}

fun die s = err s before OS.Process.exit OS.Process.failure

fun thyn i = String.concat [" vfmTest", i, "Theory"]

fun Holmake options indices = String.concat $
  OS.Path.concat(
    OS.Path.concat(Globals.HOLDIR, "bin"),
    "Holmake --keep-going" ^ options)
  :: List.map thyn indices

fun run options indices = let
  val () = ensure_fixtures ()
  val () = OS.FileSys.chDir "results"
  val options = String.concat (List.map (fn x => " " ^ x) options)
  val st = OS.Process.system $ Holmake options indices
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
         val () = system_or_fail "rm defs" "rm defs/*Script.sml"
         val () = generate_test_defs_scripts ()
         val () = TextIO.print "Generated scripts in defs\n"
         val () = system_or_fail "rm results" "rm results/*Script.sml"
         val () = generate_test_results_scripts ()
         val () = TextIO.print "Generated scripts in results\n"
       in () end
  else let
    val st = if List.exists (equal Results) options
             then OS.Process.success
             else run (List.mapPartial destOption options) indices
  in
    if OS.Process.isSuccess st
    then if List.exists (equal NoResults) options
         then ()
         else write_test_results_table () before
              TextIO.print "Results written to results/table.html\n"
    else die "runtests.exe: Holmake failed\n"
  end
end handle e => die $ String.concat [exnName e, ": ", exnMessage e, "\n"]
