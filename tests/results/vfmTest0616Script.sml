Theory vfmTest0616[no_sig_docs]
Ancestors vfmTestDefs0616
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0616_0.nsv", "result0616_1.nsv", "result0616_2.nsv", "result0616_3.nsv", "result0616_4.nsv", "result0616_5.nsv", "result0616_6.nsv", "result0616_7.nsv"];
val thyn = "vfmTestDefs0616";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
