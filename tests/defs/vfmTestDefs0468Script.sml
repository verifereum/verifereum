Theory vfmTestDefs0468[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/return.json";
val defs = mapi (define_test "0468") tests;
