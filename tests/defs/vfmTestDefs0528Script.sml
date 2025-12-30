Theory vfmTestDefs0528[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/eip2315NotRemoved.json";
val defs = mapi (define_test "0528") tests;
