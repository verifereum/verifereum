open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2292";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "2292") tests;
val () = export_theory_no_docs ();
