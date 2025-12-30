Theory vfmTestDefs2099[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_EmptyContractWithStorageAndCallIt_0wei.json";
val defs = mapi (define_test "2099") tests;
