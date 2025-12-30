Theory vfmTestDefs0287[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_system_contract_errors.json";
val defs = mapi (define_test "0287") tests;
