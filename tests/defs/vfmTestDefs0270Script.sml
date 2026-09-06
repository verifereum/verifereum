Theory vfmTestDefs0270[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_size_limit_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_size_limit_boundary.json");
val defs = mapi (define_test "0270") tests;
