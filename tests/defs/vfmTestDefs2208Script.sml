open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2208";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcallcode_001_OOGMAfter2.json";
val defs = mapi (define_test "2208") tests;
val () = export_theory_no_docs ();
