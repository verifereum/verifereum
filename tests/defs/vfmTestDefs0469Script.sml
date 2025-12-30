Theory vfmTestDefs0469[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/sstore_sload.json";
val defs = mapi (define_test "0469") tests;
