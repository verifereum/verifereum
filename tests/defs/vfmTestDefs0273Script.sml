Theory vfmTestDefs0273[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_invalid_log_length.json";
val defs = mapi (define_test "0273") tests;
