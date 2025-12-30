Theory vfmTestDefs0466[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/pc.json";
val defs = mapi (define_test "0466") tests;
