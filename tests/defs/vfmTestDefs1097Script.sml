Theory vfmTestDefs1097[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/validation/transaction/sender_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/validation/transaction/sender_balance.json");
val defs = mapi (define_test "1097") tests;
