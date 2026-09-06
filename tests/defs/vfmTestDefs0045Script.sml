Theory vfmTestDefs0045[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage/gas_usage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage/gas_usage.json");
val defs = mapi (define_test "0045") tests;
