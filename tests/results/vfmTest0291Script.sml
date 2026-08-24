Theory vfmTest0291[no_sig_docs]
Ancestors vfmTestDefs0291
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0291_0.nsv", "result0291_1.nsv", "result0291_2.nsv", "result0291_3.nsv", "result0291_4.nsv", "result0291_5.nsv", "result0291_6.nsv", "result0291_7.nsv", "result0291_8.nsv"];
val thyn = "vfmTestDefs0291";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
