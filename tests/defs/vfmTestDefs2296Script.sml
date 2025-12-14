open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2296";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecall_10_OOGE_2.json";
val defs = mapi (define_test "2296") tests;
val () = export_theory_no_docs ();
