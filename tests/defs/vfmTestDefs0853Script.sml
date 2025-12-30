Theory vfmTestDefs0853[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CodeInConstructor.json";
val defs = mapi (define_test "0853") tests;
