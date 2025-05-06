open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0279Theory;
val () = new_theory "vfmTest0279";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0279") $ get_result_defs "vfmTestDefs0279";
val () = export_theory_no_docs ();
