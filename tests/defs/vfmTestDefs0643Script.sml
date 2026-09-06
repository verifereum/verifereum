Theory vfmTestDefs0643[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create2_refund_ef/create2_refund_ef.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create2_refund_ef/create2_refund_ef.json");
val defs = mapi (define_test "0643") tests;
