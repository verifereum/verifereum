Theory vfmTestDefs0870[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/berlin/eip2929_gas_cost_increases/call/call_precompile_range_boundaries.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/berlin/eip2929_gas_cost_increases/call/call_precompile_range_boundaries.json");
val defs = mapi (define_test "0870") tests;
