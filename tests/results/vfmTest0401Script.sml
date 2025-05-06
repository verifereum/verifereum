open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0401Theory;
val () = new_theory "vfmTest0401";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0401") $ get_result_defs "vfmTestDefs0401";
val () = export_theory_no_docs ();
