open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0369Theory;
val () = new_theory "vfmTest0369";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0369") $ get_result_defs "vfmTestDefs0369";
val () = export_theory_no_docs ();
