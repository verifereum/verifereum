Theory vfmTestDefs0988[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP3607/transactionCollidingWithNonEmptyAccount_send_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP3607/transactionCollidingWithNonEmptyAccount_send_Paris.json");
val defs = mapi (define_test "0988") tests;
