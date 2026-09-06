Theory vfmTestDefs0225[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/homestead/identity_precompile/identity/identity_return_overwrite.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/homestead/identity_precompile/identity/identity_return_overwrite.json");
val defs = mapi (define_test "0225") tests;
