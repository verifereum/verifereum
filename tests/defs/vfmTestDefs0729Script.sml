Theory vfmTestDefs0729[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/base_fee_diff_places_osaka/base_fee_diff_places.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/base_fee_diff_places_osaka/base_fee_diff_places.json");
val defs = mapi (define_test "0729") tests;
