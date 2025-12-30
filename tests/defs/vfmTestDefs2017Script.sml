Theory vfmTestDefs2017[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^256-1_255.json";
val defs = mapi (define_test "2017") tests;
