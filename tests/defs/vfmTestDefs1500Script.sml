Theory vfmTestDefs1500[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP3855_push0/push0_gas/push0_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP3855_push0/push0_gas/push0_gas.json");
val defs = mapi (define_test "1500") tests;
