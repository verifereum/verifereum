structure vfmTestLib :> vfmTestLib = struct

  open HolKernel JSONDecode vfmTestAuxLib vfmTestDefLib

  val fixtures_url_prefix = String.concat [
    "https://github.com/ethereum/execution-specs/releases/download/tests%40v",
    fixtures_version, "/" ]
  val fixtures_tarball = "fixtures.tar.gz"
  val version_file = "version.txt"

  fun system_or_fail err s = let
    val st = OS.Process.system s
  in
    if OS.Process.isSuccess st then ()
    else raise Fail err
  end

  fun in_dir path f = let
    val old = OS.FileSys.getDir ()
    val () = OS.FileSys.chDir path
    val result = f () handle e => (OS.FileSys.chDir old; raise e)
  in
    result before OS.FileSys.chDir old
  end

  fun ensure_fixtures () = in_dir (test_root ()) (fn () =>
    if let val inp = TextIO.openIn (fixtures_path version_file)
       in TextIO.inputAll inp = fixtures_version
          before TextIO.closeIn inp
       end handle Io _ => false
    then ()
    else let
      val () = system_or_fail "curl_fixtures" $
        String.concat["curl -fLO ", fixtures_url_prefix ^ fixtures_tarball]
      val () = system_or_fail "rm" "rm -fr fixtures"
      val () = system_or_fail "tar_fixtures" $
        String.concat ["tar -xzf ", fixtures_tarball]
      val out = TextIO.openOut (fixtures_path version_file)
      val () = TextIO.output(out, fixtures_version)
    in
      TextIO.closeOut out
    end)

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
             (* Tests built in parallel publish their results into this
                directory by renaming temporary files, so an entry can
                vanish between readDir and isDir. *)
             else if (OS.FileSys.isDir pf
                      handle e as OS.SysErr (_, err) =>
                        if err = OS.syserror "ENOENT" then false else raise e)
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

  val test_index_entry_decoder =
    JSONDecode.map (fn (fork, format, json_path) =>
      if fork = fork_name andalso format = "blockchain_test"
      then SOME json_path
      else NONE) $
    tuple3 (field "fork" string,
            field "format" string,
            field "json_path" string)

  val test_index_decoder =
    field "test_cases" (array test_index_entry_decoder)

  fun distinct_sorted [] = []
    | distinct_sorted (x::xs) = let
        fun loop _ [] = []
          | loop previous (y::ys) =
              if y = previous then loop previous ys
              else y :: loop y ys
      in
        x :: loop x xs
      end

  fun get_all_test_json_paths () =
    fixtures_path ".meta/index.json"
    |> decodeFile test_index_decoder
    |> List.mapPartial I
    |> sort string_less
    |> distinct_sorted

  val padding = 4
  val test_defs_prefix = "vfmTestDefs"

  fun test_indices json_paths = let
    val all_paths = get_all_test_json_paths ()
    fun test_index json_path =
      padl padding #"0" $ Int.toString $ index (equal json_path) all_paths
      handle HOL_ERR _ => raise Fail $ String.concat [
        "not among the ", fork_name,
        " blockchain tests in fixtures/.meta/index.json: ", json_path ]
  in
    List.map test_index json_paths
  end

  fun test_defs_script_text index json_path = let
    val sidx = padl padding #"0" $ Int.toString index
    val thyn = String.concat [test_defs_prefix, sidx]
    val dep_path = OS.Path.concat(OS.Path.parentArc,
                     OS.Path.concat("fixtures", json_path))
    val text = String.concat [
      "Theory ", thyn, "[no_sig_docs]\nLibs vfmTestAuxLib vfmTestDefLib\n",
      "val () = holbuild_extra_deps [\"", dep_path, "\"];\n",
      "val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path \"",
      json_path, "\");\n",
      "val defs = mapi (define_test \"", sidx, "\") tests;\n"
    ]
  in
    (thyn, text)
  end

  fun test_results_script_text index json_path = let
    val sidx = padl padding #"0" $ Int.toString index
    val thyn = test_defs_prefix ^ sidx
    val rthy = "vfmTest" ^ sidx
    val test_count = List.length $ json_path_to_tests $ fixtures_path json_path
    val result_files = List.tabulate(test_count, fn test_number =>
      String.concat ["result", sidx, "_", Int.toString test_number, ".nsv"])
    val extra_outputs = String.concatWith ", " $
      List.map (fn file => "\"" ^ file ^ "\"") result_files
    val text = String.concat [
      "Theory ", rthy, "[no_sig_docs]\nAncestors ",
      thyn, "\nLibs wordsLib vfmTestAuxLib vfmTestResultLib\n",
      "val () = holbuild_extra_outputs [", extra_outputs, "];\n",
      "val thyn = \"", thyn, "\";\n",
      "val defs = get_result_defs thyn;\n",
      "val () = vfmTestLib.remove_nsv_files thyn;\n",
      "val () = List.app (ignore o save_result_thm thyn) defs;\n"
    ]
  in
    (rthy, text)
  end

  val script_suffix = "Script.sml"

  fun write_script path_for (thyn, text) = let
    val path = path_for (thyn ^ script_suffix)
    val out = TextIO.openOut path
    val () = TextIO.output (out, text)
  in
    TextIO.closeOut out
  end

  fun generate_test_defs_scripts () = let
    val json_paths = get_all_test_json_paths ()
    val named_scripts = mapi test_defs_script_text json_paths
  in
    List.app (write_script defs_path) named_scripts
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
    val (_, nsvs) = collect_files "nsv" (results_path "") ([], [])
    val result_nsvs = List.filter
      (String.isPrefix pfx o #file o OS.Path.splitDirFile) nsvs
  in
    List.app OS.FileSys.remove result_nsvs
  end

  fun generate_test_results_scripts () = let
    val json_paths = get_all_test_json_paths ()
    val named_scripts = mapi test_results_script_text json_paths
  in
    List.app (write_script results_path) named_scripts
  end

  type test_result = {
    name: string,
    result: string,
    seconds: string,
    runner: string,
    index: string
  }

  (* A result file has the lines name, result, seconds, and optionally the
     runner that produced it. The results theories write no runner line, so
     a missing one means checked. *)
  fun read_test_result_data result_file : test_result = let
    val inp = TextIO.openIn result_file
    val lines = TextIO.inputAll inp
    val () = TextIO.closeIn inp
    val (name, result, seconds, runner) =
      case String.tokens (equal #"\n") lines of
        [name, result, seconds] => (name, result, seconds, "checked")
      | [name, result, seconds, runner] =>
          if runner = "checked" orelse runner = "unchecked"
          then (name, result, seconds, runner)
          else raise Fail $ String.concat [
            result_file, ": unknown runner ", runner,
            " (expected checked or unchecked)"]
      | fields => raise Fail $ String.concat [
          result_file, ": ", Int.toString (List.length fields),
          " lines (expected name, result, seconds and optionally runner)"]
    val index = result_file |> OS.Path.splitDirFile |> #file
                            |> OS.Path.splitBaseExt |> #base
                            |> triml (String.size "result")
  in
    {name=name, result=result, seconds=seconds, runner=runner, index=index}
  end

  fun is_modified_system name = let
    val name = String.translate (String.str o Char.toLower) name
    fun cnts s = String.isSubstring s name
  in
    List.exists cnts [
      "modified_withdrawal_contract",
      "modified_consolidation_contract"
    ]
  end

  (* the CSS class of a result; table.js hides rows by these classes *)
  fun result_class result =
    if result = "Passed" then "passed"
    else if result = "Timeout" then "timeout"
    else "fail"

  fun mk_test_result_row {name, result, seconds, runner, index} = let
    val result1 = String.translate (fn c =>
                    if c = #"|" then "!" else String.str c) $
                  String.concatWith " " $
                  String.tokens Char.isSpace result
    val nametd = if is_modified_system name
                 then "<td class=modified-system>"
                 else "<td>"
  in
    String.concat [
      "<tr><td><span class=", result_class result, ">", result1,
      "</span></td><td>", seconds, "s</td>", nametd, name, "</td><td>",
      index, "</td><td>", runner, "</td></tr>\n"
    ]
  end

  fun by_name (r1: test_result) (r2: test_result) =
    string_less (#name r1) (#name r2)

  (* the command's output without surrounding whitespace, or "unknown" when
     the command cannot run or prints nothing (git outside a checkout) *)
  fun system_output (cmd, args) = let
    val proc = Unix.execute (cmd,args)
    val output = TextIO.inputAll (Unix.textInstreamOf proc)
    val () = ignore $ Unix.reap proc
    val trimmed = Substring.string $ Substring.dropl Char.isSpace $
                  Substring.dropr Char.isSpace $ Substring.full output
  in
    if trimmed = "" then "unknown" else trimmed
  end handle OS.SysErr _ => "unknown"

  (* The runner of a table: checked, unchecked, or mixed with the counts. *)
  fun table_runner (data: test_result list) = let
    val checked = List.length (List.filter (equal "checked" o #runner) data)
    val unchecked = List.length data - checked
  in
    if unchecked = 0 then "checked"
    else if checked = 0 then "unchecked"
    else String.concat ["mixed (", Int.toString checked, " checked, ",
                        Int.toString unchecked, " unchecked)"]
  end

  fun write_test_results_table table_file = let
    val dir = results_path ""
    val date = Date.fmt "%Y-%m-%d" (Date.fromTimeUniv (Time.now ()))
    val arch = system_output ("/usr/bin/uname", ["-m"])
    val commit = system_output ("/usr/bin/git", ["rev-parse", "HEAD"])
    val commit_html =
      if commit = "unknown" then commit
      else String.concat [
        "<a href=https://github.com/verifereum/verifereum/commit/", commit,
        ">", commit, "</a>"]
    val (_, nsvs) = collect_files "nsv" dir ([], [])
    val unsorted_data = List.map read_test_result_data nsvs
    val data = sort by_name unsorted_data
    val runner = table_runner data
    val out = TextIO.openOut (OS.Path.concat (dir, table_file))
    fun count cls =
      List.length (List.filter (equal cls o result_class o #result) data)
    val pass_count = count "passed"
    val total_count = List.length data
    val percentage = Real.fmt (StringCvt.FIX (SOME 1)) $
      100.0 * (Real.fromInt pass_count / Real.fromInt total_count)
    val () = TextIO.output(out, String.concat [
      "<html><head><title>Verifereum EEST Results: ", runner, "</title>",
      "<link rel=stylesheet href=table.css />",
      "<script src=table.js></script></head>\n<body>"])
    val () = TextIO.output(out, String.concat [
      "<p><a href=https://verifereum.org/>Verifereum</a> ", fork_name,
      " tests v", fixtures_version, " @", commit_html,
      ", table written ", date, " on ", arch, "</p>\n",
      "<p>Passed: ", Int.toString pass_count, "/",
      Int.toString total_count, " (", percentage, "%), timeout: ",
      Int.toString (count "timeout"), ", fail: ",
      Int.toString (count "fail"), "</p>\n",
      "<p>Runner: ", runner, ". Checked results are theorems proved in ",
      "HOL4; unchecked results come from native code generated from the ",
      "same definitions, without proof.</p>\n"])
    val () = TextIO.output(out,
      "<table><thead><tr><th>Result</th><th>Time</th><th>Name</th><th>Index</th><th>Runner</th></tr></thead><tbody>\n")
    val () = List.app (curry TextIO.output out o mk_test_result_row) data
    val () = TextIO.output(out,
      "</tbody></table></body></html>")
  in
    TextIO.closeOut out
  end

end
