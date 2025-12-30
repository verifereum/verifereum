Theory vfmTestDefs0202[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_limit_with_withdrawals.json";
val defs = mapi (define_test "0202") tests;
