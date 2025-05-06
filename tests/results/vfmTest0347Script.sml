open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0347Theory;
val () = new_theory "vfmTest0347";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0347") $ get_result_defs "vfmTestDefs0347";
val () = export_theory_no_docs ();
