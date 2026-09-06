Theory vfmTestDefs1677[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_call_to_self_sub_refund_below_zero/sstore_call_to_self_sub_refund_below_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSStoreTest/sstore_call_to_self_sub_refund_below_zero/sstore_call_to_self_sub_refund_below_zero.json");
val defs = mapi (define_test "1677") tests;
