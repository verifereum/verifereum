open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0602Theory;
val () = new_theory "vfmTest0602";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0602") $ get_result_defs "vfmTestDefs0602";
val () = export_theory_no_docs ();
