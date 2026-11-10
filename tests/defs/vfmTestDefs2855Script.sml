Theory vfmTestDefs2855[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_construction_correct/multi_owned_construction_correct.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_construction_correct/multi_owned_construction_correct.json");
val defs = mapi (define_test "2855") tests;
