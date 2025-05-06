open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0633Theory;
val () = new_theory "vfmTest0633";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0633") $ get_result_defs "vfmTestDefs0633";
val () = export_theory_no_docs ();
