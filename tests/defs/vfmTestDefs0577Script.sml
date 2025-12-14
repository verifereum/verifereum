open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0577";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeInInitcodeToEmptyContract.json";
val defs = mapi (define_test "0577") tests;
val () = export_theory_no_docs ();
