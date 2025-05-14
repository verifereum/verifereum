open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2020";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertOpcodeInCallsOnNonEmptyReturnData.json";
val defs = mapi (define_test "2020") tests;
val () = export_theory_no_docs ();
