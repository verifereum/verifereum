Theory vfmTestDefs1041[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractNoCash.json";
val defs = mapi (define_test "1041") tests;
