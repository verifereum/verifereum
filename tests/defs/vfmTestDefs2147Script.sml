Theory vfmTestDefs2147[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_change_requirement_to1/multi_owned_change_requirement_to1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_change_requirement_to1/multi_owned_change_requirement_to1.json");
val defs = mapi (define_test "2147") tests;
