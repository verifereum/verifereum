open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0197Theory;
val () = new_theory "vfmTest0197";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0197") $ get_result_defs "vfmTestDefs0197";
val () = export_theory_no_docs ();
