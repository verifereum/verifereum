open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0362";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/or.json";
val defs = mapi (define_test "0362") tests;
val () = export_theory_no_docs ();
