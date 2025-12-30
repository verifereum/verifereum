Theory vfmTestDefs0788[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_FirstByte_loop.json";
val defs = mapi (define_test "0788") tests;
