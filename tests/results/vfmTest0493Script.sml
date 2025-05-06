open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0493Theory;
val () = new_theory "vfmTest0493";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0493") $ get_result_defs "vfmTestDefs0493";
val () = export_theory_no_docs ();
