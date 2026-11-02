Theory vfmTestDefs2879[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/wallet_kill_not_by_owner/wallet_kill_not_by_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/wallet_kill_not_by_owner/wallet_kill_not_by_owner.json");
val defs = mapi (define_test "2879") tests;
