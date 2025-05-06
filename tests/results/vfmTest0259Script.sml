open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0259Theory;
val () = new_theory "vfmTest0259";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0259") $ get_result_defs "vfmTestDefs0259";
val () = export_theory_no_docs ();
