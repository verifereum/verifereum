Theory vfmTestDefs0764[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP3855_push0/push0_gas2/push0_gas2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP3855_push0/push0_gas2/push0_gas2.json");
val defs = mapi (define_test "0764") tests;
