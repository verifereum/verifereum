open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0406Theory;
val () = new_theory "vfmTest0406";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0406") $ get_result_defs "vfmTestDefs0406";
val () = export_theory_no_docs ();
