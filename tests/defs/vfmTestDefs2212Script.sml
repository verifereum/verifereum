open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2212";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_OOGMBefore2.json";
val defs = mapi (define_test "2212") tests;
val () = export_theory_no_docs ();
