Theory vfmTestDefs0977[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/addressOpcodes.json";
val defs = mapi (define_test "0977") tests;
