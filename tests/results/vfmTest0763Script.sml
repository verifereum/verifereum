open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0763Theory;
val () = new_theory "vfmTest0763";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0763") $ get_result_defs "vfmTestDefs0763";
val () = export_theory_no_docs ();
