open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2789Theory;
val () = new_theory "vfmTest2789";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2789") $ get_result_defs "vfmTestDefs2789";
val () = export_theory_no_docs ();
