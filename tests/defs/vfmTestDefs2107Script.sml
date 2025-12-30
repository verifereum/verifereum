Theory vfmTestDefs2107[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1MB1024Calldepth.json";
val defs = mapi (define_test "2107") tests;
