open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2308";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGMBefore2.json";
val defs = mapi (define_test "2308") tests;
val () = export_theory_no_docs ();
