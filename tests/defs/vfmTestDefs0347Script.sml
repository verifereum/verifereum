Theory vfmTestDefs0347[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stAttackTest/contract_creation_spam/contract_creation_spam.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stAttackTest/contract_creation_spam/contract_creation_spam.json");
val defs = mapi (define_test "0347") tests;
