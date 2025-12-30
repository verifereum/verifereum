Theory vfmTestDefs0223[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_contract_initcode.json";
val defs = mapi (define_test "0223") tests;
