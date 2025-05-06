open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0757Theory;
val () = new_theory "vfmTest0757";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0757") $ get_result_defs "vfmTestDefs0757";
val () = export_theory_no_docs ();
