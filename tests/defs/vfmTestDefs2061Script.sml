Theory vfmTestDefs2061[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_name_registrator_addres_too_big_right/callcode_to_name_registrator_addres_too_big_right.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_name_registrator_addres_too_big_right/callcode_to_name_registrator_addres_too_big_right.json");
val defs = mapi (define_test "2061") tests;
