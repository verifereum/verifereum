open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0551Theory;
val () = new_theory "vfmTest0551";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0551") $ get_result_defs "vfmTestDefs0551";
val () = export_theory_no_docs ();
