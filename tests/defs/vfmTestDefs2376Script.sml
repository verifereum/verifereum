open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2376";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecall_10_OOGE.json";
val defs = mapi (define_test "2376") tests;
val () = export_theory_no_docs ();
