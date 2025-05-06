open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0126Theory;
val () = new_theory "vfmTest0126";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0126") $ get_result_defs "vfmTestDefs0126";
val () = export_theory_no_docs ();
