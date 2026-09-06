Theory vfmTest1060[no_sig_docs]
Ancestors vfmTestDefs1060
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1060_0.nsv", "result1060_1.nsv", "result1060_2.nsv", "result1060_3.nsv", "result1060_4.nsv", "result1060_5.nsv"];
val thyn = "vfmTestDefs1060";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
