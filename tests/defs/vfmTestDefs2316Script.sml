open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2316";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcall_ABCB_RECURSIVE.json";
val defs = mapi (define_test "2316") tests;
val () = export_theory_no_docs ();
