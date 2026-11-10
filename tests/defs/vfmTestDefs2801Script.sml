Theory vfmTestDefs2801[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stTransactionTest/contract_store_clears_oog/contract_store_clears_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stTransactionTest/contract_store_clears_oog/contract_store_clears_oog.json");
val defs = mapi (define_test "2801") tests;
