open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0713Theory;
val () = new_theory "vfmTest0713";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0713") $ get_result_defs "vfmTestDefs0713";
val () = export_theory_no_docs ();
