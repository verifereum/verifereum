Theory vfmTestDefs1291[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecover1.json";
val defs = mapi (define_test "1291") tests;
