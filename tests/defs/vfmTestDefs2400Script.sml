open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2400";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_OOGMAfter.json";
val defs = mapi (define_test "2400") tests;
val () = export_theory_no_docs ();
