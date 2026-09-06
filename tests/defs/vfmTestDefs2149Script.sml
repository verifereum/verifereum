Theory vfmTestDefs2149[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_construction_correct/multi_owned_construction_correct.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_construction_correct/multi_owned_construction_correct.json");
val defs = mapi (define_test "2149") tests;
