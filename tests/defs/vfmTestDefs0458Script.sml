Theory vfmTestDefs0458[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpToPush.json";
val defs = mapi (define_test "0458") tests;
