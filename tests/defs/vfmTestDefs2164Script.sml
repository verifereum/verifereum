Theory vfmTestDefs2164[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_construction_oog/wallet_construction_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/wallet_construction_oog/wallet_construction_oog.json");
val defs = mapi (define_test "2164") tests;
