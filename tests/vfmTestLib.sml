structure vfmTestLib :> vfmTestLib = struct
  open HolKernel vfmTestAuxLib

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

  fun get_all_state_test_json_paths () =
    "fixtures/state_tests"
    |> collect_json_files_rec
    |> sort string_less

  fun state_test_defn_script_text index json_path = let
    val sidx = padl 3 #"0" $ Int.toString index
    val thyn = "vfmStateTestDefs" ^ sidx
    val text = String.concat [
      "open HolKernel vfmTestAuxLib vfmTestDefLib;\n",
      "val () = new_theory \"", thyn, "\";\n",
      "val tests = state_test_json_path_to_tests \"../../", json_path, "\";\n",
      "val defs = mapi (define_state_test \"", sidx, "\") tests;\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (thyn, text)
  end

  fun state_test_result_script_text thyn = let
    val z = String.size thyn
    val rthy = Substring.concat [
                  Substring.substring(thyn, 0, 12),
                  Substring.substring(thyn, z-3, 3)
               ]
    val text = String.concat [
      "open HolKernel vfmTestAuxLib vfmTestResultLib ", thyn, "Theory;\n",
      "val () = new_theory \"", rthy, "\";\n",
      "val () = List.app (ignore o save_result_thm default_limit \"", thyn, "\") $ ",
      "get_result_defs \"", thyn, "\";\n",
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

  fun generate_state_test_defn_scripts () = let
    val json_paths = get_all_state_test_json_paths ()
    val named_scripts = mapi state_test_defn_script_text json_paths
  in
    List.app (write_script "state/defs") named_scripts
  end

  fun generate_state_test_result_scripts () = let
    val (_, smls) = collect_files "sml" "state/defs" ([], [])
    val scripts = List.filter (String.isSuffix "Script.sml") smls
    val thyns = List.map (ss (Substring.triml 11 o Substring.trimr 10)) smls
    val named_scripts = List.map state_test_result_script_text thyns
  in
    List.app (write_script "state/results") named_scripts
  end

  type test_result = {name: string, result: string, seconds: string}

  fun read_test_result_data result_file : test_result = let
    val inp = TextIO.openIn result_file
    val line = trimr 1 $ TextIO.inputAll inp
    val () = TextIO.closeIn inp
    val [name, result, seconds] = String.fields (equal #",") line
  in
    {name=name, result=result, seconds=seconds}
  end

  fun mk_test_result_row {name, result, seconds} = let
    val success = result = "Passed"
    val result1 = String.concatWith " " $ String.tokens Char.isSpace result
    val cls = if success then "pass" else "fail"
  in
    String.concat [
      "<tr class=", cls,
      "><td>", name, "</td>",
      "<td>", result1, "</td>",
      "<td>", seconds, "s</td></tr>"
    ]
  end

  fun by_name (r1: test_result) (r2: test_result) =
    string_less (#name r1) (#name r2)

  fun write_test_results_table dir = let
    val out = TextIO.openOut (OS.Path.concat (dir, "table.html"))
    val (_, csvs) = collect_files "csv" dir ([], [])
    val unsorted_data = List.map read_test_result_data csvs
    val data = sort by_name unsorted_data
    val pass_count = List.length (List.filter (equal "Passed" o #result) data)
    val total_count = List.length data
    val percentage = Real.fmt (StringCvt.FIX (SOME 1)) $
      100.0 * (Real.fromInt pass_count / Real.fromInt total_count)
    val () = TextIO.output(out, String.concat [
      "<div class=rate>Successes: ",
        Int.toString pass_count, "/", Int.toString total_count,
        " (", percentage, "%)</div>"])
    val () = TextIO.output(out,
      "<table class=results><thead><tr><th>Name</th>" ^
      "<th>Result</th><th>Time</th></tr></thead>")
    val () = List.app (curry TextIO.output out o mk_test_result_row) data
  in
    TextIO.closeOut out
  end

  (*
    1. State tests
    2. Blockchain tests
    3. Legacy state tests (General State Tests ?)
    4. Legacy blockchain tests
    Ignoring for now: Blockchain engine tests, Transaction tests, (other) Legacy tests
  *)
end
