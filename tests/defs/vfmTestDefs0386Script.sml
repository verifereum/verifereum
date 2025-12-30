Theory vfmTestDefs0386[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_contract_creating_tx.json";
val defs = mapi (define_test "0386") tests;
