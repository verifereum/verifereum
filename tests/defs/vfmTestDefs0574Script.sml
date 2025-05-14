open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0574";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcall_000_OOGMAfter.json";
val defs = mapi (define_test "0574") tests;
val () = export_theory_no_docs ();
