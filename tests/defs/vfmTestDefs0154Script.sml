open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0154";
val tests = json_path_to_tests "../fixtures/blockchain_tests/homestead/coverage/test_coverage.json";
val defs = mapi (define_test "0154") tests;
val () = export_theory_no_docs ();
