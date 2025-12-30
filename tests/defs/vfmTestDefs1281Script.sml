Theory vfmTestDefs1281[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CALLCODESha256_4.json";
val defs = mapi (define_test "1281") tests;
