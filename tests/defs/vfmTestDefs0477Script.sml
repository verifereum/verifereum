Theory vfmTestDefs0477[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmTests/random.json";
val defs = mapi (define_test "0477") tests;
