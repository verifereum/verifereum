Theory vfmTestDefs0156[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/homestead/identity_precompile/test_identity_return_overwrite.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/homestead/identity_precompile/test_identity_return_overwrite.json");
val defs = mapi (define_test "0156") tests;
