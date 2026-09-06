Theory vfmTest0037[no_sig_docs]
Ancestors vfmTestDefs0037
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0037_0.nsv", "result0037_1.nsv", "result0037_2.nsv", "result0037_3.nsv", "result0037_4.nsv", "result0037_5.nsv", "result0037_6.nsv", "result0037_7.nsv", "result0037_8.nsv", "result0037_9.nsv", "result0037_10.nsv", "result0037_11.nsv", "result0037_12.nsv", "result0037_13.nsv", "result0037_14.nsv", "result0037_15.nsv", "result0037_16.nsv", "result0037_17.nsv", "result0037_18.nsv", "result0037_19.nsv", "result0037_20.nsv", "result0037_21.nsv", "result0037_22.nsv", "result0037_23.nsv"];
val thyn = "vfmTestDefs0037";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
