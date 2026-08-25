Theory vfmTest0478[no_sig_docs]
Ancestors vfmTestDefs0478
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0478_0.nsv", "result0478_1.nsv", "result0478_2.nsv", "result0478_3.nsv", "result0478_4.nsv", "result0478_5.nsv", "result0478_6.nsv", "result0478_7.nsv", "result0478_8.nsv", "result0478_9.nsv", "result0478_10.nsv", "result0478_11.nsv", "result0478_12.nsv", "result0478_13.nsv", "result0478_14.nsv", "result0478_15.nsv", "result0478_16.nsv"];
val thyn = "vfmTestDefs0478";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
