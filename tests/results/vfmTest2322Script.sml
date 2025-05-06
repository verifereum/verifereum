open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2322Theory;
val () = new_theory "vfmTest2322";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2322") $ get_result_defs "vfmTestDefs2322";
val () = export_theory_no_docs ();
