Theory vfmTestDefs0122[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/examples/test_block_intermediate_state.json";
val defs = mapi (define_test "0122") tests;
