Theory vfmTestDefs1285[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_oog_additional_gas_costs1/call_oog_additional_gas_costs1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCallCodes/call_oog_additional_gas_costs1/call_oog_additional_gas_costs1.json");
val defs = mapi (define_test "1285") tests;
