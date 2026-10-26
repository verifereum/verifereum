Theory vfmTestDefs3154[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/shanghai/eip3860_initcode/initcode/create2_oversized_initcode_with_insufficient_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/shanghai/eip3860_initcode/initcode/create2_oversized_initcode_with_insufficient_balance.json");
val defs = mapi (define_test "3154") tests;
