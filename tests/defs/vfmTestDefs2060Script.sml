Theory vfmTestDefs2060[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSpecialTest/JUMPDEST_Attack.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSpecialTest/JUMPDEST_Attack.json");
val defs = mapi (define_test "2060") tests;
