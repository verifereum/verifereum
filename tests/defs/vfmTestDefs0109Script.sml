Theory vfmTestDefs0109[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy/mcopy_on_empty_memory.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy/mcopy_on_empty_memory.json");
val defs = mapi (define_test "0109") tests;
