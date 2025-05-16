open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2042";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflowM1PUSH.json";
val defs = mapi (define_test "2042") tests;
val () = export_theory_no_docs ();
