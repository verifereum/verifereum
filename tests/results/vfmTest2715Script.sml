open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2715Theory;
val () = new_theory "vfmTest2715";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2715") $ get_result_defs "vfmTestDefs2715";
val () = export_theory_no_docs ();
