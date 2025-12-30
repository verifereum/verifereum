Theory vfmTestDefs1252[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODEEcrecover0_NoGas.json";
val defs = mapi (define_test "1252") tests;
