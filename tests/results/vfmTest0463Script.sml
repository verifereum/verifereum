open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0463Theory;
val () = new_theory "vfmTest0463";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0463") $ get_result_defs "vfmTestDefs0463";
val () = export_theory_no_docs ();
