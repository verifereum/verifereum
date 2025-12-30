Theory vfmTestDefs0848[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EmptyContractWithStorageAndCallIt_0wei.json";
val defs = mapi (define_test "0848") tests;
