open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0812Theory;
val () = new_theory "vfmTest0812";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0812") $ get_result_defs "vfmTestDefs0812";
val () = export_theory_no_docs ();
