Theory vfmTestDefs0468[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_name_registrator_per_txs/create_name_registrator_per_txs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_name_registrator_per_txs/create_name_registrator_per_txs.json");
val defs = mapi (define_test "0468") tests;
