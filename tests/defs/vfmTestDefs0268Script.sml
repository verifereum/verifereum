Theory vfmTestDefs0268[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip6110_deposits/test_deposit.json";
val defs = mapi (define_test "0268") tests;
