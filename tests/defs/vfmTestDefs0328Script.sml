open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0328";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3855_push0/push0Gas2.json";
val defs = mapi (define_test "0328") tests;
val () = export_theory_no_docs ();
