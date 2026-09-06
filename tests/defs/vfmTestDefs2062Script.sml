Theory vfmTestDefs2062[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_name_registrator_zero_mem_expanion/callcode_to_name_registrator_zero_mem_expanion.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_name_registrator_zero_mem_expanion/callcode_to_name_registrator_zero_mem_expanion.json");
val defs = mapi (define_test "2062") tests;
