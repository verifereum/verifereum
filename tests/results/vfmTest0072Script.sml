open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0072Theory;
val () = new_theory "vfmTest0072";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0072") $ get_result_defs "vfmTestDefs0072";
val () = export_theory_no_docs ();
