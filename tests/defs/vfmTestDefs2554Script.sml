open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2554";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/NoSrcAccount.json";
val defs = mapi (define_test "2554") tests;
val () = export_theory_no_docs ();
