Theory vfmTestDefs2410[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToReturn1ForDynamicJump1.json";
val defs = mapi (define_test "2410") tests;
