open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0303";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/multiple_withdrawals_same_address.json";
val defs = mapi (define_test "0303") tests;
val () = export_theory_no_docs ();
