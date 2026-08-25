Theory vfmTestDefs1008[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashChangedAccount.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashChangedAccount.json");
val defs = mapi (define_test "1008") tests;
