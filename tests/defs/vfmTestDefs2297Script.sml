open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2297";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcodecall_110_OOGE.json";
val defs = mapi (define_test "2297") tests;
val () = export_theory_no_docs ();
