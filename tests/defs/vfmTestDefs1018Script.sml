open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1018";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log4_logMemsizeZero.json";
val defs = mapi (define_test "1018") tests;
val () = export_theory_no_docs ();
