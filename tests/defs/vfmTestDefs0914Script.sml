open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0914";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExample/invalidTr.json";
val defs = mapi (define_test "0914") tests;
val () = export_theory_no_docs ();
