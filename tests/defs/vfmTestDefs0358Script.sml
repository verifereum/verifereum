open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0358";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/gt.json";
val defs = mapi (define_test "0358") tests;
val () = export_theory_no_docs ();
