Theory vfmTestDefs2112[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/opcodes_transaction_init/opcodes_transaction_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/opcodes_transaction_init/opcodes_transaction_init.json");
val defs = mapi (define_test "2112") tests;
