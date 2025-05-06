open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0994Theory;
val () = new_theory "vfmTest0994";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0994") $ get_result_defs "vfmTestDefs0994";
val () = export_theory_no_docs ();
