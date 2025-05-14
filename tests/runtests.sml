open HolKernel GetOpt vfmTestLib

val usage_header = String.concat [
  "runtests.exe [<num> ...]\n",
  "Run Verifereum on the EEST suite. If numbers are provided,\n",
  "only run those tests, otherwise run all tests."
]

fun err s = TextIO.output(TextIO.stdErr, s)

val cline_options = [
  {short = "h",
   long = ["help"],
   desc = NoArg (K ()),
   help = "print help"}
]
val cline_config = {
  argOrder = Permute,
  options = cline_options,
  errFn = err
}
val usage = usageInfo {header=usage_header, options=cline_options}

fun die s = err s before OS.Process.exit OS.Process.failure

fun thyn i = String.concat [" vfmTest", i, "Theory"]

fun Holmake indices = String.concat $
  OS.Path.concat(
    OS.Path.concat(Globals.HOLDIR, "bin"),
    "Holmake") :: List.map thyn indices

fun main () = let
  val (options, indices) = GetOpt.getOpt cline_config $ CommandLine.arguments()
  val curd = OS.FileSys.getDir()
in
  if (not o equal "tests") $ #file $ OS.Path.splitDirFile $ OS.FileSys.getDir()
  then die "error: must be run from the tests directory\n"
  else if not (List.null options)
  then TextIO.print usage
  else let
    val () = ensure_fixtures ()
    val () = OS.FileSys.chDir "results"
    val st = OS.Process.system $ Holmake indices
    val () = OS.FileSys.chDir OS.Path.parentArc
  in
    if OS.Process.isSuccess st
    then write_test_results_table () before
         TextIO.print "results written to results/table.html\n"
    else die "runtests.exe: Holmake failed"
  end
end handle e => die $ String.concat [exnName e, ": ", exnMessage e]
