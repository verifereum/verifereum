open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0543Theory;
val () = new_theory "vfmTest0543";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0543") $ get_result_defs "vfmTestDefs0543";
val () = export_theory_no_docs ();
