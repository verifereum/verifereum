Theory vfmTestDefs0976[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/valid_inputs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip4844_blobs/point_evaluation_precompile/valid_inputs.json");
val defs = mapi (define_test "0976") tests;
