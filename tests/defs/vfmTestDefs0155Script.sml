Theory vfmTestDefs0155[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/homestead/identity_precompile/test_identity_return_buffer_modify.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/homestead/identity_precompile/test_identity_return_buffer_modify.json");
val defs = mapi (define_test "0155") tests;
