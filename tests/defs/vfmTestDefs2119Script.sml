Theory vfmTestDefs2119[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallContractToCreateContractOOG.json";
val defs = mapi (define_test "2119") tests;
