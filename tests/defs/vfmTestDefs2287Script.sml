open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2287";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_SuicideEnd2.json";
val defs = mapi (define_test "2287") tests;
val () = export_theory_no_docs ();
