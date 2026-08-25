Theory vfmTestDefs0202[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_limit_with_withdrawals.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_limit_with_withdrawals.json");
val defs = mapi (define_test "0202") tests;
