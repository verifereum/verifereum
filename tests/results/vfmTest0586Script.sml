open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0586Theory;
val () = new_theory "vfmTest0586";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0586") $ get_result_defs "vfmTestDefs0586";
val () = export_theory_no_docs ();
