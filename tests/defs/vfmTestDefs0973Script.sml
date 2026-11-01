Theory vfmTestDefs0973[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/external_vectors.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/external_vectors.json");
val defs = mapi (define_test "0973") tests;
