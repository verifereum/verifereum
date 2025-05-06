open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0860Theory;
val () = new_theory "vfmTest0860";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0860") $ get_result_defs "vfmTestDefs0860";
val () = export_theory_no_docs ();
