open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2259";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcode_01_SuicideEnd2.json";
val defs = mapi (define_test "2259") tests;
val () = export_theory_no_docs ();
