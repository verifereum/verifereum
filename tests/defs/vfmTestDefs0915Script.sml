open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0915";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/labelsExample.json";
val defs = mapi (define_test "0915") tests;
val () = export_theory_no_docs ();
