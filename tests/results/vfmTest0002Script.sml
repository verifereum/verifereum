open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0002Theory;
val () = new_theory "vfmTest0002";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0002") $ get_result_defs "vfmTestDefs0002";
val () = export_theory_no_docs ();
