Theory vfmTestDefs1748[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ecrecover0_overlapping_input_output/callcode_ecrecover0_overlapping_input_output.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_ecrecover0_overlapping_input_output/callcode_ecrecover0_overlapping_input_output.json");
val defs = mapi (define_test "1748") tests;
