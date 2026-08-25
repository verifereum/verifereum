Theory vfmTestDefs0385[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip3855_push0/test_push0_contracts.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip3855_push0/test_push0_contracts.json");
val defs = mapi (define_test "0385") tests;
