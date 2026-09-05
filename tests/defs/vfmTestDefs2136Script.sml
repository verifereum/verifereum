Theory vfmTestDefs2136[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/day_limit_construction_partial/day_limit_construction_partial.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/day_limit_construction_partial/day_limit_construction_partial.json");
val defs = mapi (define_test "2136") tests;
