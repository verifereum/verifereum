Theory vfmTestDefs0398[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcode_in_initcode_to_exis_contract_with_v_transfer_ne_money/callcode_in_initcode_to_exis_contract_with_v_transfer_ne_money.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcode_in_initcode_to_exis_contract_with_v_transfer_ne_money/callcode_in_initcode_to_exis_contract_with_v_transfer_ne_money.json");
val defs = mapi (define_test "0398") tests;
