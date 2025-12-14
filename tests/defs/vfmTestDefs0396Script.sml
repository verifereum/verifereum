open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0396";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_self_destructing_account.json";
val defs = mapi (define_test "0396") tests;
val () = export_theory_no_docs ();
