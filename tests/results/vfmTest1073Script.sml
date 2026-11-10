Theory vfmTest1073[no_sig_docs]
Ancestors vfmTestDefs1073
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1073_0.nsv", "result1073_1.nsv", "result1073_2.nsv", "result1073_3.nsv", "result1073_4.nsv", "result1073_5.nsv", "result1073_6.nsv", "result1073_7.nsv"];
val thyn = "vfmTestDefs1073";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
