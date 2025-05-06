open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2236Theory;
val () = new_theory "vfmTest2236";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2236") $ get_result_defs "vfmTestDefs2236";
val () = export_theory_no_docs ();
