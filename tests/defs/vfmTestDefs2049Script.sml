Theory vfmTestDefs2049[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_out_of_gas/call_to_name_registrator_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_name_registrator_out_of_gas/call_to_name_registrator_out_of_gas.json");
val defs = mapi (define_test "2049") tests;
