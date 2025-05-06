open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2159";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stacksanitySWAP.json";
val defs = mapi (define_test "2159") tests;
val () = export_theory_no_docs ();
