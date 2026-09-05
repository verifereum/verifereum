Theory vfmTestDefs2444[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip3860_initcode/initcode/create2_oversized_initcode_with_insufficient_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip3860_initcode/initcode/create2_oversized_initcode_with_insufficient_balance.json");
val defs = mapi (define_test "2444") tests;
