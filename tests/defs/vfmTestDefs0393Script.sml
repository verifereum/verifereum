open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0393";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/test_multiple_withdrawals_same_address.json";
val defs = mapi (define_test "0393") tests;
val () = export_theory_no_docs ();
