open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0401";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_zero_amount.json";
val defs = mapi (define_test "0401") tests;
val () = export_theory_no_docs ();
