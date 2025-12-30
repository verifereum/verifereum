Theory vfmTestDefs2295[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecall_10_OOGE.json";
val defs = mapi (define_test "2295") tests;
