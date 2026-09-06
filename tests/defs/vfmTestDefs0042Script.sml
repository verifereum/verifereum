Theory vfmTestDefs0042[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/basic_tload/basic_tload_works.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/basic_tload/basic_tload_works.json");
val defs = mapi (define_test "0042") tests;
