open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0091Theory;
val () = new_theory "vfmTest0091";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0091") $ get_result_defs "vfmTestDefs0091";
val () = export_theory_no_docs ();
