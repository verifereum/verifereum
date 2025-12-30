Theory vfmTestDefs0858[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGFromEOARefunds.json";
val defs = mapi (define_test "0858") tests;
