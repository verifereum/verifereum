Theory vfmTestDefs2070[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_name_registrator_out_of_memory_bonds1/create_name_registrator_out_of_memory_bonds1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_name_registrator_out_of_memory_bonds1/create_name_registrator_out_of_memory_bonds1.json");
val defs = mapi (define_test "2070") tests;
