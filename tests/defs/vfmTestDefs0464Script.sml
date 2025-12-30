Theory vfmTestDefs0464[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/mstore.json";
val defs = mapi (define_test "0464") tests;
