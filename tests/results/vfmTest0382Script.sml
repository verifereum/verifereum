open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0382Theory;
val () = new_theory "vfmTest0382";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0382") $ get_result_defs "vfmTestDefs0382";
val () = export_theory_no_docs ();
