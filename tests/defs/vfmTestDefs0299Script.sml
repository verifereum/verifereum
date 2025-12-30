Theory vfmTestDefs0299[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_account_warming.json";
val defs = mapi (define_test "0299") tests;
