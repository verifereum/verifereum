open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2570";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndInternalCallSuicidesOOG.json";
val defs = mapi (define_test "2570") tests;
val () = export_theory_no_docs ();
