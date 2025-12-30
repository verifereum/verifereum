Theory vfmTestDefs0844[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EmptyContractAndCallIt_0wei.json";
val defs = mapi (define_test "0844") tests;
