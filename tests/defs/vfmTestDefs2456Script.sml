Theory vfmTestDefs2456[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/sstore_combinations_initial11_2_Paris.json";
val defs = mapi (define_test "2456") tests;
