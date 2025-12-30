Theory vfmTestDefs0981[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/storageCosts.json";
val defs = mapi (define_test "0981") tests;
