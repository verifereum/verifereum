Theory vfmTestDefs2128[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransitionTest/create_name_registrator_per_txs_after/create_name_registrator_per_txs_after.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransitionTest/create_name_registrator_per_txs_after/create_name_registrator_per_txs_after.json");
val defs = mapi (define_test "2128") tests;
