open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2568";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndSendMoneyToItselfEtherDestroyed.json";
val defs = mapi (define_test "2568") tests;
val () = export_theory_no_docs ();
