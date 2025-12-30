Theory vfmTestDefs1257[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover2.json";
val defs = mapi (define_test "1257") tests;
