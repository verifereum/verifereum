Theory vfmTestDefs2093[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/test_name_registrator/test_name_registrator.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/test_name_registrator/test_name_registrator.json");
val defs = mapi (define_test "2093") tests;
