Theory vfmTestDefs1007[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashCALLCODE.json";
val defs = mapi (define_test "1007") tests;
