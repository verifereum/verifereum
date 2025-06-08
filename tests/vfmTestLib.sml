structure vfmTestLib :> vfmTestLib = struct

  open HolKernel vfmTestAuxLib

  val fixtures_url_prefix = String.concat [
    "https://github.com/ethereum/execution-spec-tests/releases/download/v",
    fixtures_version, "/" ]
  val static_tarball = "fixtures_static.tar.gz"
  val develop_tarball = "fixtures_develop.tar.gz"
  val version_file = OS.Path.concat("fixtures", "version.txt")

  fun system_or_fail err s = let
    val st = OS.Process.system s
  in
    if OS.Process.isSuccess st then ()
    else raise Fail err
  end

  fun ensure_fixtures () =
    if let val inp = TextIO.openIn version_file
       in TextIO.inputAll inp = fixtures_version
          before TextIO.closeIn inp
       end handle Io _ => false
    then ()
    else let
      val () = system_or_fail "curl_static" $
        String.concat["curl -LO ", fixtures_url_prefix ^ static_tarball]
      val () = system_or_fail "curl_develop" $
        String.concat["curl -LO ", fixtures_url_prefix ^ develop_tarball]
      val () = system_or_fail "rm" "rm -fr fixtures"
      val () = system_or_fail "tar_static" $
        String.concat ["tar -xzf ", static_tarball]
      val () = system_or_fail "tar_develop" $
        String.concat ["tar -xzf", develop_tarball]
      val out = TextIO.openOut version_file
      val () = TextIO.output(out, fixtures_version)
    in
      TextIO.closeOut out
    end

  fun collect_files suffix path (dirs, files) = let
    val ds = OS.FileSys.openDir path
    fun loop (dirs, files) =
      case OS.FileSys.readDir ds of
           NONE => (dirs, files)
         | SOME file => loop let
             val pf = OS.Path.concat (path, file)
           in
             if OS.Path.ext file = SOME suffix
             then (dirs, pf::files)
             else if OS.FileSys.isDir pf
             then (pf::dirs, files)
             else (dirs, files)
           end
  in
    loop (dirs, files)
    before OS.FileSys.closeDir ds
  end

  val collect_json_files = collect_files "json"

  fun collect_json_files_rec start_path = let
    fun loop [] jsons = jsons
      | loop (path::paths_left) jsons = let
          val (dirs, jsons) = collect_json_files path (paths_left, jsons)
        in loop dirs jsons end
  in
    loop [start_path] []
  end

  fun get_all_test_json_paths () =
    "fixtures/blockchain_tests"
    |> collect_json_files_rec
    |> sort string_less

  val padding = 4
  val test_defs_prefix = "vfmTestDefs"

  fun test_defs_script_text index json_path = let
    val sidx = padl padding #"0" $ Int.toString index
    val thyn = String.concat [test_defs_prefix, sidx]
    val rpth = OS.Path.concat(OS.Path.parentArc, json_path)
    val text = String.concat [
      "open HolKernel vfmTestAuxLib vfmTestDefLib;\n",
      "val () = new_theory \"", thyn, "\";\n",
      "val tests = json_path_to_tests \"", rpth, "\";\n",
      "val defs = mapi (define_test \"", sidx, "\") tests;\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (thyn, text)
  end

  fun test_results_script_text thyn = let
    val z = String.size thyn
    val rthy = Substring.concat [
                  Substring.full "vfmTest",
                  Substring.substring(thyn, z-padding, padding)
               ]
    val text = String.concat [
      "open HolKernel wordsLib vfmTestResultLib ", thyn, "Theory;\n",
      "val () = new_theory \"", rthy, "\";\n",
      "val thyn = \"", thyn, "\";\n",
      "val defs = get_result_defs thyn;\n",
      "val () = vfmTestLib.remove_nsv_files thyn;\n",
      "val () = List.app (ignore o save_result_thm thyn) defs;\n",
      "val () = vfmTestAuxLib.export_theory_no_docs ();\n"
    ]
  in
    (rthy, text)
  end

  val script_suffix = "Script.sml"

  fun write_script dir (thyn, text) = let
    val path = OS.Path.concat(dir, thyn ^ script_suffix)
    val out = TextIO.openOut path
    val () = TextIO.output (out, text)
  in
    TextIO.closeOut out
  end

  fun generate_test_defs_scripts () = let
    val json_paths = get_all_test_json_paths ()
    val named_scripts = mapi test_defs_script_text json_paths
  in
    List.app (write_script "defs") named_scripts
  end

  fun collect_script_files dir = let
    val (_, smls) = collect_files "sml" dir ([], [])
  in
     List.filter (String.isSuffix script_suffix) $
     List.map (#file o OS.Path.splitDirFile) smls
  end

  fun remove_nsv_files thyn = let
    val z = String.size thyn
    val pfx = Substring.concat [
                Substring.full "result",
                Substring.substring(thyn, z-padding, padding),
                Substring.full "_"
              ]
    val (_, nsvs) = collect_files "nsv" "." ([], [])
    val result_nsvs = List.filter (String.isPrefix pfx) $
                      List.map (#file o OS.Path.splitDirFile) nsvs
  in
    List.app OS.FileSys.remove result_nsvs
  end

  fun generate_test_results_scripts () = let
    val scripts = collect_script_files "defs"
    val thyns = List.map (trimr (String.size script_suffix)) scripts
    val named_scripts = List.map test_results_script_text thyns
  in
    List.app (write_script "results") named_scripts
  end

  type test_result = {
    name: string,
    result: string,
    seconds: string,
    index: string
  }

  fun read_test_result_data result_file : test_result = let
    val inp = TextIO.openIn result_file
    val lines = TextIO.inputAll inp
    val () = TextIO.closeIn inp
    val [name, result, seconds] = String.tokens (equal #"\n") lines
    val index = result_file |> OS.Path.splitDirFile |> #file
                            |> OS.Path.splitBaseExt |> #base
                            |> triml (String.size "result")
  in
    {name=name, result=result, seconds=seconds, index=index}
  end

  fun is_precompile name = let
    val name = String.translate (String.str o Char.toLower) name
    fun cnts s = String.isSubstring s name
  in
    List.exists cnts [
      "precomp",
      "ecmul", "ecadd", "ecpair", "pairing", "ecrec",
      "pointadd", "pointmul", "ripemd", "blake"
    ]
  end

  fun mk_test_result_row {name, result, seconds, index} = let
    val success = result = "Passed"
    val result1 = String.translate (fn c =>
                    if c = #"|" then "!" else String.str c) $
                  String.concatWith " " $
                  String.tokens Char.isSpace result
    val cls = if success then "passed"
              else if result = "Timeout" then "timeout"
              else "fail"
    val nametd = if is_precompile name
                 then "<td class=precompile>"
                 else "<td>"
  in
    String.concat [
      "<tr><td><span class=", cls, ">", result1, "</span></td><td>",
      seconds, "s</td>", nametd, name, "</td><td>", index,
      "</td></tr>\n"
    ]
  end

  fun by_name (r1: test_result) (r2: test_result) =
    string_less (#name r1) (#name r2)

  fun system_output (cmd, args) = let
    val proc = Unix.execute (cmd,args)
  in
    TextIO.inputAll (Unix.textInstreamOf proc)
    before ignore $ Unix.reap proc
  end handle OS.SysErr _ => "unknown"

  fun write_test_results_table () = let
    val dir = "results"
    val uname = system_output ("/usr/bin/uname", ["-nor"])
    val commit = system_output ("/usr/bin/git", ["rev-parse", "HEAD"])
    val out = TextIO.openOut (OS.Path.concat (dir, "table.html"))
    val (_, nsvs) = collect_files "nsv" dir ([], [])
    val unsorted_data = List.map read_test_result_data nsvs
    val data = sort by_name unsorted_data
    val pass_count = List.length (List.filter (equal "Passed" o #result) data)
    val total_count = List.length data
    val percentage = Real.fmt (StringCvt.FIX (SOME 1)) $
      100.0 * (Real.fromInt pass_count / Real.fromInt total_count)
    val () = TextIO.output(out, String.concat [
      "<html><head><title>Verifereum EEST Results</title>",
      "<link rel=stylesheet href=table.css />",
      "<script src=table.js></script></head>\n<body>"])
    val () = TextIO.output(out, String.concat [
      "<p>", fork_name, " tests v", fixtures_version,
      " @", commit, " on ", uname, "</p>\n<p>Successes: ",
      Int.toString pass_count, "/",
      Int.toString total_count,
      " (", percentage, "%)</p>\n"])
    val () = TextIO.output(out,
      "<table><thead><tr><th>Result</th><th>Time</th><th>Name</th><th>Index</th></tr></thead><tbody>\n")
    val () = List.app (curry TextIO.output out o mk_test_result_row) data
    val () = TextIO.output(out,
      "</tbody></table></body></html>")
  in
    TextIO.closeOut out
  end

end
