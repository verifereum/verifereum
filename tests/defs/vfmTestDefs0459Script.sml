Theory vfmTestDefs0459[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpi.json";
val defs = mapi (define_test "0459") tests;
