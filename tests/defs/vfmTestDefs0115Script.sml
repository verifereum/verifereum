Theory vfmTestDefs0115[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy_memory_expansion/mcopy_memory_expansion.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy_memory_expansion/mcopy_memory_expansion.json");
val defs = mapi (define_test "0115") tests;
