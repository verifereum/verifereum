open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0306";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/self_destructing_account.json";
val defs = mapi (define_test "0306") tests;
val () = export_theory_no_docs ();
