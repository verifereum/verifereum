Theory vfmTestDefs0020[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_subcall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_subcall.json");
val defs = mapi (define_test "0020") tests;
