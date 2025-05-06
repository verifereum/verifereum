open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0094Theory;
val () = new_theory "vfmTest0094";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0094") $ get_result_defs "vfmTestDefs0094";
val () = export_theory_no_docs ();
