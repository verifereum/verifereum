Theory vfmTestDefs1040[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractAndCallItOOG.json";
val defs = mapi (define_test "1040") tests;
