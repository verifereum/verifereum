open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2266";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGMAfter.json";
val defs = mapi (define_test "2266") tests;
val () = export_theory_no_docs ();
