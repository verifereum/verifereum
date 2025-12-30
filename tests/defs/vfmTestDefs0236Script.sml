Theory vfmTestDefs0236[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/paris/security/test_tx_selfdestruct_balance_bug.json";
val defs = mapi (define_test "0236") tests;
