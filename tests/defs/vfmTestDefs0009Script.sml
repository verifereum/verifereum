Theory vfmTestDefs0009[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/byzantium/eip198_modexp_precompile/test_modexp.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/byzantium/eip198_modexp_precompile/test_modexp.json");
val defs = mapi (define_test "0009") tests;
