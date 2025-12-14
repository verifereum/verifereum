open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0580";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeInInitcodeToExistingContractWithValueTransfer.json";
val defs = mapi (define_test "0580") tests;
val () = export_theory_no_docs ();
