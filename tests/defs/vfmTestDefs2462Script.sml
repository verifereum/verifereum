Theory vfmTestDefs2462[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/ContractStoreClearsOOG.json";
val defs = mapi (define_test "2462") tests;
