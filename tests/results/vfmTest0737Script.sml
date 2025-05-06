open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0737Theory;
val () = new_theory "vfmTest0737";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0737") $ get_result_defs "vfmTestDefs0737";
val () = export_theory_no_docs ();
