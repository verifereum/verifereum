open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0859Theory;
val () = new_theory "vfmTest0859";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0859") $ get_result_defs "vfmTestDefs0859";
val () = export_theory_no_docs ();
