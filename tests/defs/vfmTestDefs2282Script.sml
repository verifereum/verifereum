open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2282";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_OOGMAfter_1.json";
val defs = mapi (define_test "2282") tests;
val () = export_theory_no_docs ();
