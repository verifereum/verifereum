open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2401";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_OOGMAfter2.json";
val defs = mapi (define_test "2401") tests;
val () = export_theory_no_docs ();
