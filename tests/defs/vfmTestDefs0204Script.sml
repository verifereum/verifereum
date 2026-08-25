Theory vfmTestDefs0204[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_rlp_size_at_limit_with_all_typed_transactions.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_rlp_size_at_limit_with_all_typed_transactions.json");
val defs = mapi (define_test "0204") tests;
