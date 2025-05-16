open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0892";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toEpmtyParis.json";
val defs = mapi (define_test "0892") tests;
val () = export_theory_no_docs ();
