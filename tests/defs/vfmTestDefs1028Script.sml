open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1028";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/add11_yml.json";
val defs = mapi (define_test "1028") tests;
val () = export_theory_no_docs ();
