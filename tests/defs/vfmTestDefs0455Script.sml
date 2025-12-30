Theory vfmTestDefs0455[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/codecopy.json";
val defs = mapi (define_test "0455") tests;
