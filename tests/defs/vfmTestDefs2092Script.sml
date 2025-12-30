Theory vfmTestDefs2092[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_ABAcallsSuicide1.json";
val defs = mapi (define_test "2092") tests;
