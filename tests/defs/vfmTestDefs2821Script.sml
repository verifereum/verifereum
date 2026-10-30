Theory vfmTestDefs2821[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stTransactionTest/store_clears_and_internal_call_store_clears_success/store_clears_and_internal_call_store_clears_success.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stTransactionTest/store_clears_and_internal_call_store_clears_success/store_clears_and_internal_call_store_clears_success.json");
val defs = mapi (define_test "2821") tests;
