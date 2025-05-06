open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0908Theory;
val () = new_theory "vfmTest0908";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0908") $ get_result_defs "vfmTestDefs0908";
val () = export_theory_no_docs ();
