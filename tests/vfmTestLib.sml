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
      "val () = List.app (ignore o save_result_thm default_limit) $ ",
      "get_result_defs \"", thyn, "\";\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (rthy, text)
  end

  fun write_script dir (thyn, text) = let
    val path = dir ^ thyn ^ "Script.sml"
    val out = TextIO.openOut path
    val () = TextIO.output (out, text)
  in
    TextIO.closeOut out
  end

  fun generate_state_test_defn_scripts () = let
    val json_paths = get_all_state_test_json_paths ()
    val named_scripts = mapi state_test_defn_script_text json_paths
  in
    List.app (write_script "state/defs/") named_scripts
  end

  fun generate_state_test_result_scripts () = let
    val (_, smls) = collect_files "sml" "state/defs" ([], [])
    val scripts = List.filter (String.isSuffix "Script.sml") smls
    val thyns = List.map (ss (Substring.triml 11 o Substring.trimr 10)) smls
    val named_scripts = List.map state_test_result_script_text thyns
  in
    List.app (write_script "state/results/") named_scripts
  end

  (* TODO: delete?
  fun define_state_tests range_start range_length = let
    val all_json_paths = get_all_state_test_json_paths ();
    val json_paths = List.drop(all_json_paths, range_start)
    val paths_in_range = if range_length < List.length json_paths
                         then List.take(json_paths, range_length)
                         else json_paths
    val tests = List.concat (List.map state_test_json_path_to_tests paths_in_range)
  in
    mapi (define_state_test (Int.toString range_start)) tests
  end
  *)

  (*
    Treat each of these separately:
    1. State tests
       a. Pick test naming scheme, maybe numbered
          with actual name as a string constant?
       b. Define components of test as HOL constants (produce theory with these
          definitions)
       c. CV-translate these constants, using caching and deep embeddings where
          appropriate (produce theory with these translations, could be same as
          above)
       d. Define HOL function that checks a state test following the consumption
          instructions, and cv-translate it.
       e. cv-eval test-checking function on all the tests (produce theory that
          includes these theorems for passing tests, and reports on failing tests
          too)
    2. Blockchain tests
    3. Legacy state tests (General State Tests ?)
    4. Legacy blockchain tests
    Ignoring for now: Blockchain engine tests, Transaction tests, (other) Legacy tests
  *)
end
