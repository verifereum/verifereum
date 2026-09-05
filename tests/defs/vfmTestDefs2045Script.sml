Theory vfmTestDefs2045[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_address_too_big_right/call_to_name_registrator_address_too_big_right.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_address_too_big_right/call_to_name_registrator_address_too_big_right.json");
val defs = mapi (define_test "2045") tests;
