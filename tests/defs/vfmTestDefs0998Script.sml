open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0998";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_logMemsizeZero.json";
val defs = mapi (define_test "0998") tests;
val () = export_theory_no_docs ();
