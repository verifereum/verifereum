Theory vfmTestDefs1009[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_static_context_same_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct_finalization/selfdestruct_static_context_same_tx.json");
val defs = mapi (define_test "1009") tests;
