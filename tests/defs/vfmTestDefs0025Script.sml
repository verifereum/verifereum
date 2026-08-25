Theory vfmTestDefs0025[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tload_reentrancy.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_tload_reentrancy.json");
val defs = mapi (define_test "0025") tests;
