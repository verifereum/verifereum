Theory vfmTestDefs2259[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcode_01_SuicideEnd2.json";
val defs = mapi (define_test "2259") tests;
