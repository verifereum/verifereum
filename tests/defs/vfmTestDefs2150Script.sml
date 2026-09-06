Theory vfmTestDefs2150[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_construction_not_enough_gas/multi_owned_construction_not_enough_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_construction_not_enough_gas/multi_owned_construction_not_enough_gas.json");
val defs = mapi (define_test "2150") tests;
