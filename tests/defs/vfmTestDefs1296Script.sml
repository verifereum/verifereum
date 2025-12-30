Theory vfmTestDefs1296[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverCheckLengthWrongV.json";
val defs = mapi (define_test "1296") tests;
