Theory vfmTestDefs1969[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSLoadTest/sloadGasCost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSLoadTest/sloadGasCost.json");
val defs = mapi (define_test "1969") tests;
