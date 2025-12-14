open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0204";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_rlp_size_at_limit_with_all_typed_transactions.json";
val defs = mapi (define_test "0204") tests;
val () = export_theory_no_docs ();
