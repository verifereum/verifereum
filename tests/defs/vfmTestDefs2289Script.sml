open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2289";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_SuicideEnd2.json";
val defs = mapi (define_test "2289") tests;
val () = export_theory_no_docs ();
