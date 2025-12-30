Theory vfmTestDefs0123[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/identity_precompile/test_call_identity_precompile.json";
val defs = mapi (define_test "0123") tests;
