open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2291";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_ABCB_RECURSIVE2.json";
val defs = mapi (define_test "2291") tests;
val () = export_theory_no_docs ();
