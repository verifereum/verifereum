open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0629";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcodecall_110_OOGMAfter.json";
val defs = mapi (define_test "0629") tests;
val () = export_theory_no_docs ();
