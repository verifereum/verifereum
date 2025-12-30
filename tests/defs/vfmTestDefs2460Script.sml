Theory vfmTestDefs2460[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/sstore_combinations_initial21_2_Paris.json";
val defs = mapi (define_test "2460") tests;
