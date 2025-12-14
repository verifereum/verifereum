open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2478";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/NoSrcAccountCreate1559.json";
val defs = mapi (define_test "2478") tests;
val () = export_theory_no_docs ();
