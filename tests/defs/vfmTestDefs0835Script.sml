Theory vfmTestDefs0835[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE2_CallData.json";
val defs = mapi (define_test "0835") tests;
