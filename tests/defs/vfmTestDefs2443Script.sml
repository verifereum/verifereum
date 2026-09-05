Theory vfmTestDefs2443[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip3860_initcode/initcode/contract_creating_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip3860_initcode/initcode/contract_creating_tx.json");
val defs = mapi (define_test "2443") tests;
