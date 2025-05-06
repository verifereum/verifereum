open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0932Theory;
val () = new_theory "vfmTest0932";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0932") $ get_result_defs "vfmTestDefs0932";
val () = export_theory_no_docs ();
