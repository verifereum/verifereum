Theory vfmTestDefs0842[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_EContract_ThenCALLToNonExistentAcc.json";
val defs = mapi (define_test "0842") tests;
