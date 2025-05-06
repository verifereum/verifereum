open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0479Theory;
val () = new_theory "vfmTest0479";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0479") $ get_result_defs "vfmTestDefs0479";
val () = export_theory_no_docs ();
