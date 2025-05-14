open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1022";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP3607/transactionCollidingWithNonEmptyAccount_calls.json";
val defs = mapi (define_test "1022") tests;
val () = export_theory_no_docs ();
