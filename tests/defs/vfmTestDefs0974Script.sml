Theory vfmTestDefs0974[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/invalid_inputs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/invalid_inputs.json");
val defs = mapi (define_test "0974") tests;
