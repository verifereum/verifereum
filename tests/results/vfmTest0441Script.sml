open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0441Theory;
val () = new_theory "vfmTest0441";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0441") $ get_result_defs "vfmTestDefs0441";
val () = export_theory_no_docs ();
