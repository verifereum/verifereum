Theory vfmTestDefs0446[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/eq.json";
val defs = mapi (define_test "0446") tests;
