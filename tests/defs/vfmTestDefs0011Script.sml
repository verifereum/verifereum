Theory vfmTestDefs0011[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_gasprice.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_basic_tload_gasprice.json");
val defs = mapi (define_test "0011") tests;
