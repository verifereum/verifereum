open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0347";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/signextend.json";
val defs = mapi (define_test "0347") tests;
val () = export_theory_no_docs ();
