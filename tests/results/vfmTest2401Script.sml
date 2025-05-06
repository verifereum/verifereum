open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2401Theory;
val () = new_theory "vfmTest2401";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2401") $ get_result_defs "vfmTestDefs2401";
val () = export_theory_no_docs ();
