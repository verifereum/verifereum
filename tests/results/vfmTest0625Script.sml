open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0625Theory;
val () = new_theory "vfmTest0625";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0625") $ get_result_defs "vfmTestDefs0625";
val () = export_theory_no_docs ();
