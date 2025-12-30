Theory vfmTestDefs2281[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcodecallcode_011_OOGMAfter2.json";
val defs = mapi (define_test "2281") tests;
