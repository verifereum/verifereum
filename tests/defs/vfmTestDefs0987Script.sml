open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0987";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log1_logMemStartTooHigh.json";
val defs = mapi (define_test "0987") tests;
val () = export_theory_no_docs ();
