open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0301";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/large_amount.json";
val defs = mapi (define_test "0301") tests;
val () = export_theory_no_docs ();
