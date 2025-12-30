Theory vfmTestDefs0959[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/gasPriceDiffPlaces.json";
val defs = mapi (define_test "0959") tests;
