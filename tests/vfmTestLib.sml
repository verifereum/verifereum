structure vfmTestLib :> vfmTestLib = struct

  open HolKernel vfmTestAuxLib

  val fixtures_url_prefix =
    "https://github.com/ethereum/execution-spec-tests/releases/download/v4.4.0/"
  val static_tarball = "fixtures_static.tar.gz"
  val develop_tarball = "fixtures_develop.tar.gz"

  fun ensure_fixtures () =
    if OS.FileSys.isDir "fixtures" handle SysErr _ => false
    then ()
    else let
      val curl_static = OS.Process.system $
        String.concat["curl -LO ", fixtures_url_prefix ^ static_tarball]
      val curl_develop = OS.Process.system $
        String.concat["curl -LO ", fixtures_url_prefix ^ develop_tarball]
      val tar_static = OS.Process.system $
        String.concat ["tar -xzf ", static_tarball]
      val tar_develop = OS.Process.system $
        String.concat ["tar -xzf", develop_tarball]
    in
      if List.all OS.Process.isSuccess [
        curl_static, curl_develop, tar_static, tar_develop
      ] then () else raise Fail "ensure_fixtures"
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
      "open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib ", thyn, "Theory;\n",
      "val () = new_theory \"", rthy, "\";\n",
      "val thyn = \"", thyn, "\";\n",
      "val defs = get_result_defs thyn;\n",
      "val () = List.app (ignore o save_result_thm default_limit thyn) defs;\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (rthy, text)
  end

  fun write_script dir (thyn, text) = let
    val path = OS.Path.concat(dir, thyn ^ "Script.sml")
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

  fun generate_test_results_scripts () = let
    val (_, smls) = collect_files "sml" "defs" ([], [])
    val script_suffix = "Script.sml"
    val scripts = List.filter (String.isSuffix script_suffix) $
                  List.map (#file o OS.Path.splitDirFile) smls
    val thyns = List.map (trimr (String.size script_suffix)) scripts
    val named_scripts = List.map test_results_script_text thyns
  in
    List.app (write_script "results") named_scripts
  end

  type test_result = {name: string, result: string, seconds: string}

  fun read_test_result_data result_file : test_result = let
    val inp = TextIO.openIn result_file
    val lines = TextIO.inputAll inp
    val () = TextIO.closeIn inp
    val [name, result, seconds] = String.tokens (equal #"\n") lines
  in
    {name=name, result=result, seconds=seconds}
  end

  fun mk_test_result_row {name, result, seconds} = let
    val success = result = "Passed"
    val result1 = String.concatWith " " $ String.tokens Char.isSpace result
    val cls = if success then "pass" else "fail"
  in
    String.concat [
      name, " | [",
      result1, "]{.", cls, "} | ",
      seconds, "s\n"
    ]
  end

  fun by_name (r1: test_result) (r2: test_result) =
    string_less (#name r1) (#name r2)

  fun write_test_results_table () = let
    val dir = "results"
    val out = TextIO.openOut (OS.Path.concat (dir, "table.md"))
    val (_, nsvs) = collect_files "nsv" dir ([], [])
    val unsorted_data = List.map read_test_result_data nsvs
    val data = sort by_name unsorted_data
    val pass_count = List.length (List.filter (equal "Passed" o #result) data)
    val total_count = List.length data
    val percentage = Real.fmt (StringCvt.FIX (SOME 1)) $
      100.0 * (Real.fromInt pass_count / Real.fromInt total_count)
    val () = TextIO.output(out, String.concat [
      "Successes: ",
      Int.toString pass_count, "/",
      Int.toString total_count,
      " (", percentage, "%)\n\n"])
    val () = TextIO.output(out,
      String.concat [
        "Name | Result | Time\n",
        "------|---|-\n"
      ])
    val () = List.app (curry TextIO.output out o mk_test_result_row) data
  in
    TextIO.closeOut out
  end

end
