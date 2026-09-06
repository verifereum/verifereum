Theory vfmTestDefs2052[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_too_much_memory2/call_to_name_registrator_too_much_memory2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_too_much_memory2/call_to_name_registrator_too_much_memory2.json");
val defs = mapi (define_test "2052") tests;
