Theory vfmTestDefs2068[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_name_registrator_oog_mem_expansion_oov/create_name_registrator_oog_mem_expansion_oov.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/create_name_registrator_oog_mem_expansion_oov/create_name_registrator_oog_mem_expansion_oov.json");
val defs = mapi (define_test "2068") tests;
