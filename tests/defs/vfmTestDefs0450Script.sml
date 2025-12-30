Theory vfmTestDefs0450[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/not.json";
val defs = mapi (define_test "0450") tests;
