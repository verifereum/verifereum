Theory vfmTestDefs0673[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/transaction_collision/transaction_collision.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/transaction_collision/transaction_collision.json");
val defs = mapi (define_test "0673") tests;
