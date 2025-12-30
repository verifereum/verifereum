Theory vfmTestDefs0148[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/scenarios/test_scenarios.json";
val defs = mapi (define_test "0148") tests;
