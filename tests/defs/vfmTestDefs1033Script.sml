Theory vfmTestDefs1033[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSubcallSuicideCancun.json";
val defs = mapi (define_test "1033") tests;
