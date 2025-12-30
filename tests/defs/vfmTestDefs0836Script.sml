Theory vfmTestDefs0836[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE2_RefundEF.json";
val defs = mapi (define_test "0836") tests;
