open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0992";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/eip1559.json";
val defs = mapi (define_test "0992") tests;
val () = export_theory_no_docs ();
