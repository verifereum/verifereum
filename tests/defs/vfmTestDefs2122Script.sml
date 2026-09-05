Theory vfmTestDefs2122[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_stop_after_suicide/suicides_stop_after_suicide.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/suicides_stop_after_suicide/suicides_stop_after_suicide.json");
val defs = mapi (define_test "2122") tests;
