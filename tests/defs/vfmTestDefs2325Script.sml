open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2325";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_SuicideEnd.json";
val defs = mapi (define_test "2325") tests;
val () = export_theory_no_docs ();
