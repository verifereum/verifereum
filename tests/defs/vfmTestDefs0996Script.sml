open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0996";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_logMemStartTooHigh.json";
val defs = mapi (define_test "0996") tests;
val () = export_theory_no_docs ();
