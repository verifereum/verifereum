open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0676Theory;
val () = new_theory "vfmTest0676";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0676") $ get_result_defs "vfmTestDefs0676";
val () = export_theory_no_docs ();
