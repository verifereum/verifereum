Theory vfmTestDefs1261[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecoverR_prefixed0.json";
val defs = mapi (define_test "1261") tests;
