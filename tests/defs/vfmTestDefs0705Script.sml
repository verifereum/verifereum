Theory vfmTestDefs0705[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/create_and_gas_inside_create/create_and_gas_inside_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/create_and_gas_inside_create/create_and_gas_inside_create.json");
val defs = mapi (define_test "0705") tests;
