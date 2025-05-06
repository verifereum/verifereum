open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0296";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip4895_withdrawals/withdrawals/balance_within_block.json";
val defs = mapi (define_test "0296") tests;
val () = export_theory_no_docs ();
