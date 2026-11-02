Theory vfmTestDefs1767[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_sha256_4_gas99/callcode_sha256_4_gas99.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stPreCompiledContracts2/callcode_sha256_4_gas99/callcode_sha256_4_gas99.json");
val defs = mapi (define_test "1767") tests;
