open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2330";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_ABCB_RECURSIVE2.json";
val defs = mapi (define_test "2330") tests;
val () = export_theory_no_docs ();
