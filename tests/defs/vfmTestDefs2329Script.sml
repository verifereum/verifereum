open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2329";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_SuicideMiddle.json";
val defs = mapi (define_test "2329") tests;
val () = export_theory_no_docs ();
