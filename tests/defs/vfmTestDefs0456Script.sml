Theory vfmTestDefs0456[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/gas.json";
val defs = mapi (define_test "0456") tests;
