open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0689Theory;
val () = new_theory "vfmTest0689";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0689") $ get_result_defs "vfmTestDefs0689";
val () = export_theory_no_docs ();
