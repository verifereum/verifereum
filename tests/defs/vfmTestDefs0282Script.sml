Theory vfmTestDefs0282[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_consolidation_requests_during_fork.json";
val defs = mapi (define_test "0282") tests;
