Theory vfmTestDefs0453[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/slt.json";
val defs = mapi (define_test "0453") tests;
