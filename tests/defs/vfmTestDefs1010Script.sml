Theory vfmTestDefs1010[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_to_self_keeps_existing_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_to_self_keeps_existing_balance.json");
val defs = mapi (define_test "1010") tests;
