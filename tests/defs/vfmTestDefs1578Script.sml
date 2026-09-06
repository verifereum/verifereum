Theory vfmTestDefs1578[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stRefundTest/refund_max/refund_max.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stRefundTest/refund_max/refund_max.json");
val defs = mapi (define_test "1578") tests;
