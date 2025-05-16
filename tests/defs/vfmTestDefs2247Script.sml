open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2247";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_OOGMBefore.json";
val defs = mapi (define_test "2247") tests;
val () = export_theory_no_docs ();
