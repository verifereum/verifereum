open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0298";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/initcode/gas_usage.json";
val defs = mapi (define_test "0298") tests;
val () = export_theory_no_docs ();
