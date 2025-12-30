Theory vfmTestDefs0447[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/gt.json";
val defs = mapi (define_test "0447") tests;
