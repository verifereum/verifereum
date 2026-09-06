Theory vfmTestDefs2044[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_address_too_big_left/call_to_name_registrator_address_too_big_left.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_address_too_big_left/call_to_name_registrator_address_too_big_left.json");
val defs = mapi (define_test "2044") tests;
