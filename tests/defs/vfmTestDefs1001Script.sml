Theory vfmTestDefs1001[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/codeCopyZero_Paris.json";
val defs = mapi (define_test "1001") tests;
