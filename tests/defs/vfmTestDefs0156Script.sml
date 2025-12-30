Theory vfmTestDefs0156[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/homestead/identity_precompile/test_identity_return_overwrite.json";
val defs = mapi (define_test "0156") tests;
