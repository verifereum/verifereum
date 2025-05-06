open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0566";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00_OOGE_valueTransfer.json";
val defs = mapi (define_test "0566") tests;
val () = export_theory_no_docs ();
