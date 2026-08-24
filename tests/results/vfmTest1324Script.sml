Theory vfmTest1324[no_sig_docs]
Ancestors vfmTestDefs1324
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1324_0.nsv", "result1324_1.nsv", "result1324_2.nsv", "result1324_3.nsv", "result1324_4.nsv", "result1324_5.nsv"];
val thyn = "vfmTestDefs1324";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
