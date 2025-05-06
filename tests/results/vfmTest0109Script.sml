open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0109Theory;
val () = new_theory "vfmTest0109";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0109") $ get_result_defs "vfmTestDefs0109";
val () = export_theory_no_docs ();
