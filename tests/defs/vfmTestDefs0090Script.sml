Theory vfmTestDefs0090[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip5656_mcopy/test_mcopy_huge_memory_expansion.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip5656_mcopy/test_mcopy_huge_memory_expansion.json");
val defs = mapi (define_test "0090") tests;
