Theory vfmTestDefs2095[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/contract_store_clears_oog/contract_store_clears_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/contract_store_clears_oog/contract_store_clears_oog.json");
val defs = mapi (define_test "2095") tests;
