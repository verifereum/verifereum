Theory vfmTestDefs0219[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/validation/transaction/sender_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/validation/transaction/sender_balance.json");
val defs = mapi (define_test "0219") tests;
