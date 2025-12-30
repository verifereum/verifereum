Theory vfmTestDefs2479[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/Opcodes_TransactionInit.json";
val defs = mapi (define_test "2479") tests;
