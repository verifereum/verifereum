Theory vfmTestDefs0271[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_extra_logs.json";
val defs = mapi (define_test "0271") tests;
