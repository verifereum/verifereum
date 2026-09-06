Theory vfmTestDefs0111[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy/valid_mcopy_operations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip5656_mcopy/mcopy/valid_mcopy_operations.json");
val defs = mapi (define_test "0111") tests;
