open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2230";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecall_010_OOGMAfter_3.json";
val defs = mapi (define_test "2230") tests;
val () = export_theory_no_docs ();
