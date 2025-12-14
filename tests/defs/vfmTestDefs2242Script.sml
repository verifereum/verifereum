open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2242";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_OOGE.json";
val defs = mapi (define_test "2242") tests;
val () = export_theory_no_docs ();
