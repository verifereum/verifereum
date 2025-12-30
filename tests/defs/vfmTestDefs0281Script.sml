Theory vfmTestDefs0281[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_consolidation_requests.json";
val defs = mapi (define_test "0281") tests;
