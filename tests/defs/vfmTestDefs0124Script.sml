Theory vfmTestDefs0124[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/identity_precompile/test_call_identity_precompile_large_params.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/identity_precompile/test_call_identity_precompile_large_params.json");
val defs = mapi (define_test "0124") tests;
