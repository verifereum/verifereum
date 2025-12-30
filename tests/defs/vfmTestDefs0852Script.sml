Theory vfmTestDefs0852[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_empty000CreateinInitCode_Transaction.json";
val defs = mapi (define_test "0852") tests;
