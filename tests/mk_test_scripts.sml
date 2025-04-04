open HolKernel bossLib vfmTestLib

fun sanitize_name str =
    implode (map (fn c =>
        if Char.isAlphaNum c then c
        else #"_"
    ) (explode str))

fun make_theory_name parents filename =
    let
        val sanitized_parents = map sanitize_name parents
        val base_filename = sanitize_name (OS.Path.base filename)
    in
        String.concat (sanitized_parents @ [base_filename ^ "_Setup"])
    end

fun generate_theory_script base_dir parents filename =
let
    val theory_name = make_theory_name parents filename
    (* Construct the full directory path *)
    val full_dir_path =
        foldl (fn (p, acc) => OS.Path.concat(acc, p)) "" parents
    (* Construct the full file path *)
    val full_file_path = OS.Path.concat(full_dir_path, filename)
    val script_content =
    "open HolKernel boolLib bossLib Parse wordsLib vfmTestLib\n\n" ^
    "val () = new_theory \"" ^ theory_name ^ "\";\n\n" ^
    "val (num_tests, prove_test) = mk_prove_test \"../" ^ full_dir_path ^ "/" ^ filename ^ "\";\n" ^
    "val thms = List.tabulate (num_tests, prove_test);\n\n" ^
    "val () = export_theory_no_docs();\n"
    val output_filename = OS.Path.concat(base_dir, theory_name ^ "Script.sml")
in
    let
        val outstream = TextIO.openOut output_filename
    in
        TextIO.output(outstream, script_content);
        TextIO.closeOut outstream;
        print ("Generated theory script: " ^ output_filename ^ "\n")
    end
end

fun generate_theory_scripts base_dir tree =
    let
        fun go parents tree =
            case tree of
                TestDir (dirname, subtrees) =>
                    List.concat (map (go (parents @ [dirname])) subtrees)
              | TestFixture filename =>
                    (generate_theory_script base_dir parents filename; [filename])
    in
        go [] tree
    end

val fixtures = collect_fixtures "BlockchainTests/GeneralStateTests/"
val _ = generate_theory_scripts "theories/" fixtures
