Theory vfmTestDefs0389[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_legacy_create_edge_code_size.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip3860_initcode/test_legacy_create_edge_code_size.json");
val defs = mapi (define_test "0389") tests;
