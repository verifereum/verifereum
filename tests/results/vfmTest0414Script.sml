open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0414Theory;
val () = new_theory "vfmTest0414";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0414") $ get_result_defs "vfmTestDefs0414";
val () = export_theory_no_docs ();
