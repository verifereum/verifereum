Theory vfmTestDefs0070[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip4844_blobs/test_invalid_inputs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip4844_blobs/test_invalid_inputs.json");
val defs = mapi (define_test "0070") tests;
