open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0997";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_logMemsizeTooHigh.json";
val defs = mapi (define_test "0997") tests;
val () = export_theory_no_docs ();
