Theory vfmTestDefs1032[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSubcallSuicide.json";
val defs = mapi (define_test "1032") tests;
