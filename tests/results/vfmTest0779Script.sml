Theory vfmTest0779[no_sig_docs]
Ancestors vfmTestDefs0779
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0779_0.nsv", "result0779_1.nsv", "result0779_2.nsv", "result0779_3.nsv", "result0779_4.nsv", "result0779_5.nsv", "result0779_6.nsv", "result0779_7.nsv", "result0779_8.nsv", "result0779_9.nsv", "result0779_10.nsv", "result0779_11.nsv", "result0779_12.nsv", "result0779_13.nsv", "result0779_14.nsv", "result0779_15.nsv", "result0779_16.nsv", "result0779_17.nsv", "result0779_18.nsv", "result0779_19.nsv", "result0779_20.nsv", "result0779_21.nsv"];
val thyn = "vfmTestDefs0779";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
