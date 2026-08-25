Theory vfmTestDefs0203[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_size_limit_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7934_block_rlp_limit/test_block_at_rlp_size_limit_boundary.json");
val defs = mapi (define_test "0203") tests;
