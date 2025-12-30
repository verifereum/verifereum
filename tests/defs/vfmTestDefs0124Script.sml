Theory vfmTestDefs0124[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/identity_precompile/test_call_identity_precompile_large_params.json";
val defs = mapi (define_test "0124") tests;
