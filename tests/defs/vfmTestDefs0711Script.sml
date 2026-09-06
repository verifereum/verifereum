Theory vfmTestDefs0711[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/transaction64_rule_integer_boundaries/transaction64_rule_integer_boundaries.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/transaction64_rule_integer_boundaries/transaction64_rule_integer_boundaries.json");
val defs = mapi (define_test "0711") tests;
