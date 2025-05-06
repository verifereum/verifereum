open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0991Theory;
val () = new_theory "vfmTest0991";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0991") $ get_result_defs "vfmTestDefs0991";
val () = export_theory_no_docs ();
