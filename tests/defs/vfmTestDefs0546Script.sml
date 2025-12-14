open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0546";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcall_000_OOGMBefore.json";
val defs = mapi (define_test "0546") tests;
val () = export_theory_no_docs ();
