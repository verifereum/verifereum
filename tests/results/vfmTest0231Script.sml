open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0231Theory;
val () = new_theory "vfmTest0231";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0231") $ get_result_defs "vfmTestDefs0231";
val () = export_theory_no_docs ();
