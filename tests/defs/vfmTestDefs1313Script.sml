Theory vfmTestDefs1313[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallSha256_1.json";
val defs = mapi (define_test "1313") tests;
