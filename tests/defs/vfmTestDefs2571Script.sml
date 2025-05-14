open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2571";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndInternalCallSuicidesSuccess.json";
val defs = mapi (define_test "2571") tests;
val () = export_theory_no_docs ();
