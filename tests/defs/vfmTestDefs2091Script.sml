Theory vfmTestDefs2091[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ABAcallsSuicide0.json";
val defs = mapi (define_test "2091") tests;
