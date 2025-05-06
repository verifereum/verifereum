open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0203Theory;
val () = new_theory "vfmTest0203";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0203") $ get_result_defs "vfmTestDefs0203";
val () = export_theory_no_docs ();
