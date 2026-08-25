Theory vfmTestDefs1870[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallA_OOG.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRefundTest/refund_CallA_OOG.json");
val defs = mapi (define_test "1870") tests;
