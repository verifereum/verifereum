Theory vfmTestDefs0196[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/call_and_callcode_gas_calculation/value_transfer_gas_calculation.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/call_and_callcode_gas_calculation/value_transfer_gas_calculation.json");
val defs = mapi (define_test "0196") tests;
