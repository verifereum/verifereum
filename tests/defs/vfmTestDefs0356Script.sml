Theory vfmTestDefs0356[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/call_oog_additional_gas_costs1/call_oog_additional_gas_costs1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/call_oog_additional_gas_costs1/call_oog_additional_gas_costs1.json");
val defs = mapi (define_test "0356") tests;
