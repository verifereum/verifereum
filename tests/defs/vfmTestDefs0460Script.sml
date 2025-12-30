Theory vfmTestDefs0460[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/loop_stacklimit.json";
val defs = mapi (define_test "0460") tests;
