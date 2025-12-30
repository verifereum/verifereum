Theory vfmTestDefs1309[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallRipemd160_4.json";
val defs = mapi (define_test "1309") tests;
