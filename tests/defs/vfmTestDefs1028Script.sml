Theory vfmTestDefs1028[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSTATICCALL.json";
val defs = mapi (define_test "1028") tests;
