Theory vfmTest1647[no_sig_docs]
Ancestors vfmTestDefs1647
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1647_0.nsv", "result1647_1.nsv", "result1647_2.nsv", "result1647_3.nsv"];
val thyn = "vfmTestDefs1647";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
