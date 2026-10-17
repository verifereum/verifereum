Theory vfmTestDefs2303[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip6110_deposits/deposits/deposit_high_count.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip6110_deposits/deposits/deposit_high_count.json");
val defs = mapi (define_test "2303") tests;
