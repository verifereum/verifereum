Theory vfmTestDefs2299[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100.json";
val defs = mapi (define_test "2299") tests;
