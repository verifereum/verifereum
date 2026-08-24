Theory vfmTest0623[no_sig_docs]
Ancestors vfmTestDefs0623
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0623_0.nsv", "result0623_1.nsv", "result0623_2.nsv"];
val thyn = "vfmTestDefs0623";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
