Theory vfmTestDefs0125[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/identity_precompile/test_identity_precompile_returndata.json";
val defs = mapi (define_test "0125") tests;
