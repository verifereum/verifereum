Theory vfmTestDefs0222[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_contract_creation_transaction.json";
val defs = mapi (define_test "0222") tests;
