open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0120";
val tests = json_path_to_tests "../fixtures/blockchain_tests/homestead/coverage/coverage/coverage.json";
val defs = mapi (define_test "0120") tests;
val () = export_theory_no_docs ();
