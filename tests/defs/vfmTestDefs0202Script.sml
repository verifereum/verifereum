open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0202";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_limit_with_withdrawals.json";
val defs = mapi (define_test "0202") tests;
val () = export_theory_no_docs ();
