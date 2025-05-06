open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0454Theory;
val () = new_theory "vfmTest0454";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0454") $ get_result_defs "vfmTestDefs0454";
val () = export_theory_no_docs ();
