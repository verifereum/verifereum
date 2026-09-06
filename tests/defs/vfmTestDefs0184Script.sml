Theory vfmTestDefs0184[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/identity_precompile/identity/call_identity_precompile.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/identity_precompile/identity/call_identity_precompile.json");
val defs = mapi (define_test "0184") tests;
