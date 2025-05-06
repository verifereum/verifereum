open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0022Theory;
val () = new_theory "vfmTest0022";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0022") $ get_result_defs "vfmTestDefs0022";
val () = export_theory_no_docs ();
