Theory vfmTestDefs2285[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_OOGMBefore2.json";
val defs = mapi (define_test "2285") tests;
