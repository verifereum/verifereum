open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0952";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_integerBoundaries.json";
val defs = mapi (define_test "0952") tests;
val () = export_theory_no_docs ();
