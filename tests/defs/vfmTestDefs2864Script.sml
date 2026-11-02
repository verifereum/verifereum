Theory vfmTestDefs2864[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_revoke_nothing/multi_owned_revoke_nothing.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_revoke_nothing/multi_owned_revoke_nothing.json");
val defs = mapi (define_test "2864") tests;
